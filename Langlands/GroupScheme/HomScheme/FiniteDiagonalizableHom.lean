import Langlands.GroupScheme.HomScheme.FiniteSourceHom
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.Torus.DiagonalizableHopf

/-! # Homomorphisms out of a finite power of roots of unity -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.FiniteDiagonalizable

open Langlands.FiniteBialgebraHom FiniteSource

section Characters

variable (I : Type u) [Fintype I] [DecidableEq I] (m : ℕ) (M : Type v) [CommMonoid M]

omit [Fintype I] in
/-- A character of `(ℤ/m)^I` sends each basis vector to an `m`-th root of unity. -/
theorem apply_single_pow (χ : Multiplicative (I → ZMod m) →* Mˣ) (i : I) :
    χ (.ofAdd (Pi.single i 1)) ^ m = 1 := by
  have h : m • (Pi.single i (1 : ZMod m) : I → ZMod m) = 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [← map_pow, ← ofAdd_nsmul, h, ofAdd_zero, map_one]

variable {I m M}

/-- The additive character of `ℤ/m` attached to an `m`-th root of unity. -/
def rootHom (ζ : rootsOfUnity m M) : ZMod m →+ Additive Mˣ :=
  ZMod.lift m ⟨zmultiplesHom (Additive Mˣ) (Additive.ofMul (ζ : Mˣ)), by
    change ((m : ℤ) • Additive.ofMul (ζ : Mˣ)) = 0
    rw [← ofMul_zpow, zpow_natCast, (mem_rootsOfUnity m _).mp ζ.2, ofMul_one]⟩

theorem rootHom_intCast (ζ : rootsOfUnity m M) (k : ℤ) :
    Additive.toMul (rootHom ζ (k : ZMod m)) = (ζ : Mˣ) ^ k := by
  rw [rootHom, ZMod.lift_coe]
  rfl

/-- The character of `(ℤ/m)^I` with prescribed values on the basis vectors. -/
def charOfRoots (t : I → rootsOfUnity m M) : Multiplicative (I → ZMod m) →* Mˣ where
  toFun x := ∏ i, Additive.toMul (rootHom (t i) (x.toAdd i))
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Pi.add_apply, map_add, toMul_add, Finset.prod_mul_distrib]

theorem charOfRoots_single (t : I → rootsOfUnity m M) (i : I) (a : ZMod m) :
    charOfRoots t (.ofAdd (Pi.single i a)) = Additive.toMul (rootHom (t i) a) := by
  change ∏ j, Additive.toMul (rootHom (t j) ((Pi.single i a : I → ZMod m) j)) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

omit [Fintype I] in
theorem ofAdd_single_intCast (i : I) (k : ℤ) :
    (Multiplicative.ofAdd (Pi.single i (k : ZMod m)) : Multiplicative (I → ZMod m)) =
      (Multiplicative.ofAdd (Pi.single i 1)) ^ k := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow, toAdd_ofAdd, toAdd_ofAdd]
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

variable (I m M)

/-- Characters of `(ℤ/m)^I` with values in `Mˣ` are `I`-indexed families of `m`-th roots of
unity in `M`. -/
def rootsCharEquiv : (Multiplicative (I → ZMod m) →* Mˣ) ≃* (I → rootsOfUnity m M) where
  toFun χ i := ⟨χ (.ofAdd (Pi.single i 1)), (mem_rootsOfUnity m _).mpr (apply_single_pow I m M χ i)⟩
  invFun := charOfRoots
  left_inv χ := by
    apply MonoidHom.ext
    intro x
    have hx : x = ∏ i, Multiplicative.ofAdd (Pi.single i (x.toAdd i)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_ofAdd]
      exact (Finset.univ_sum_single x.toAdd).symm
    conv_rhs => rw [hx]
    rw [map_prod]
    change ∏ i, _ = _
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (x.toAdd i)
    rw [← hk, rootHom_intCast, ofAdd_single_intCast, map_zpow]
  right_inv t := by
    funext i
    apply Subtype.ext
    change charOfRoots t (.ofAdd (Pi.single i 1)) = (t i : Mˣ)
    rw [charOfRoots_single, ← Int.cast_one, rootHom_intCast, zpow_one]
  map_mul' χ ψ := rfl

theorem rootsCharEquiv_apply_coe (χ : Multiplicative (I → ZMod m) →* Mˣ) (i : I) :
    (rootsCharEquiv I m M χ i : Mˣ) = χ (.ofAdd (Pi.single i 1)) :=
  rfl

end Characters

section Points

variable (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I] (m : ℕ)

/-- The finite power `μ_m^I` over `Spec R`, as a product of actual group schemes. -/
abbrev muPower : GroupScheme (Spec (CommRingCat.of R)) :=
  pi fun _ : I => (mu (Spec (CommRingCat.of R)) m).toGrp

/-- Restriction of families of `m`-th roots of unity along a morphism of test schemes. -/
abbrev rootsRestrict {T T' : Over (Spec (CommRingCat.of R))} (a : T' ⟶ T) :
    (I → rootsOfUnity m Γ(T.left, ⊤)) →* (I → rootsOfUnity m Γ(T'.left, ⊤)) :=
  (restrictRootsOfUnity a.left.appTop.hom m).compLeft I

/-- Points of the diagonalizable group scheme of `(ℤ/m)^I` are families of roots of unity. -/
def diagonalizablePointsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (Diagonalizable.groupScheme (CommRingCat.of R) (I → ZMod m)).X) ≃*
      (I → rootsOfUnity m Γ(T.left, ⊤)) :=
  (Corepresented.pointsEquiv (Diagonalizable.functor (CommRingCat.of R) (I → ZMod m))
    (Diagonalizable.grpCorepresentation (CommRingCat.of R) (I → ZMod m)) T).trans
    (rootsCharEquiv I m ((algΓ (CommRingCat.of R)).obj T).unop)

theorem diagonalizablePointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of R))}
    (a : T' ⟶ T) (x : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of R) (I → ZMod m)).X) :
    diagonalizablePointsEquiv R I m T' (a ≫ x) =
      rootsRestrict R I m a (diagonalizablePointsEquiv R I m T x) := by
  change rootsCharEquiv I m _ (Corepresented.pointsEquiv _ _ T' (a ≫ x)) = _
  erw [Corepresented.pointsEquiv_naturality]
  rfl

/-- Points of `μ_m^I` are families of roots of unity. -/
def muPowerPointsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (muPower R I m).X) ≃* (I → rootsOfUnity m Γ(T.left, ⊤)) :=
  (piPointsEquiv (fun _ : I => (mu (Spec (CommRingCat.of R)) m).toGrp) T).trans
    (MulEquiv.piCongrRight fun _ => mu.pointsEquiv (Spec (CommRingCat.of R)) m T)

omit [DecidableEq I] in
theorem muPowerPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of R))} (a : T' ⟶ T)
    (x : T ⟶ (muPower R I m).X) :
    muPowerPointsEquiv R I m T' (a ≫ x) =
      rootsRestrict R I m a (muPowerPointsEquiv R I m T x) := by
  funext i
  change mu.pointsEquiv _ m T' ((a ≫ x) ≫ _) = _
  rw [Category.assoc, mu.pointsEquiv_naturality]
  rfl

/-- The diagonalizable group scheme of `(ℤ/m)^I` is the finite power `μ_m^I`. -/
def diagonalizableIso :
    (Diagonalizable.groupScheme (CommRingCat.of R) (I → ZMod m)).toGrp ≅ muPower R I m :=
  isoOfPointModels (fun T : Over (Spec (CommRingCat.of R)) => I → rootsOfUnity m Γ(T.left, ⊤))
    (fun a => rootsRestrict R I m a) (diagonalizablePointsEquiv R I m)
    (muPowerPointsEquiv R I m) (diagonalizablePointsEquiv_naturality R I m)
    (muPowerPointsEquiv_naturality R I m)

/-- The Hopf spectrum of the group algebra `R[(ℤ/m)^I]` is the finite power `μ_m^I`. -/
def muPowerHopfIso : hopfGroup R (AddMonoidAlgebra R (I → ZMod m)) ≅ muPower R I m :=
  Diagonalizable.hopfSpecIso (CommRingCat.of R) (I → ZMod m) ≪≫ diagonalizableIso R I m

end Points

section Coordinates

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]

/-- The Hopf spectrum of the coordinate Hopf algebra of an affine group scheme is the group
scheme itself. -/
def coordinateIso : hopfGroup R (AffineCoordinates.hopfAlgebra G) ≅ G :=
  (hopfSpec (CommRingCat.of R)).mapIso (CommHopfAlgCat.ofIsoSelf _).symm.op ≪≫
    AffineCoordinates.hopfSpecIso G

/-- The coordinate Hopf algebra of an affine group scheme locally of finite presentation is
finitely presented. -/
theorem finitePresentation_hopfAlgebra [LocallyOfFinitePresentation G.X.hom] :
    Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G) := by
  let eX : (hopfGroup R (AffineCoordinates.hopfAlgebra G)).X ≅ G.X :=
    (Grp.forget _).mapIso (coordinateIso G)
  have : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
  have h : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (AffineCoordinates.hopfAlgebra G)))) := by
    change LocallyOfFinitePresentation (hopfGroup R (AffineCoordinates.hopfAlgebra G)).X.hom
    rw [← Over.w eX.hom]
    infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at h
  exact RingHom.finitePresentation_algebraMap.mp h

end Coordinates

section Universal

variable (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I] (m : ℕ) [NeZero m]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [LocallyOfFinitePresentation G.X.hom]

instance : Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G) :=
  finitePresentation_hopfAlgebra G

/-- The base of the universal family of homomorphisms `μ_m^I → G`. -/
abbrev homAlgebra : Type u :=
  HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R (I → ZMod m))

/-- The universal family of homomorphisms `μ_m^I → G` over `Spec (homAlgebra R I m G)`. -/
def universalHom : RelativeHom (muPower R I m) G (specOver R (homAlgebra R I m G)) :=
  transport (muPowerHopfIso R I m).symm (coordinateIso G) (universalFamily R _ _)

theorem isUniversal_universalHom : IsUniversal (universalHom R I m G) :=
  (isUniversal_universalFamily R _ _).transport _ _

end Universal

/-- **Representability of homomorphisms out of `μ_m^I`.** For an affine group scheme `G`
locally of finite presentation over `Spec R`, a finite index type `I` and `m > 0`, the
functor of homomorphisms `μ_m^I → G` is represented by an affine scheme locally of finite
presentation over `Spec R`. -/
theorem exists_isUniversal_muPower (R : Type u) [CommRing R] (I : Type u) [Finite I] {m : ℕ}
    (hm : 0 < m) (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] :
    ∃ (Y : Over (Spec (CommRingCat.of R)))
      (i : RelativeHom (pi fun _ : I => (mu (Spec (CommRingCat.of R)) m).toGrp) G Y),
      IsUniversal i ∧ IsAffine Y.left ∧ LocallyOfFinitePresentation Y.hom := by
  have : NeZero m := ⟨hm.ne'⟩
  have := Fintype.ofFinite I
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  refine ⟨specOver R (homAlgebra R I m G), universalHom R I m G,
    isUniversal_universalHom R I m G, inferInstanceAs (IsAffine (Spec _)), ?_⟩
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R _)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end Langlands.GroupScheme.HomScheme.FiniteDiagonalizable
