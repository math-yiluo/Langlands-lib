import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.PseudoComplete
import Langlands.GroupScheme.SplitSolvable
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Fixed points at the end of an elementary orbit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace OrbitLimit

/-- Two morphisms from an affine scheme to a separated scheme agree when they agree
after a morphism that is injective on global sections. -/
theorem ext_of_injective_appTop {S : Scheme.{u}} {T Y W : Over S} [IsSeparated Y.hom]
    [IsAffine T.left] (f g : T ⟶ Y) (j : W ⟶ T) (hj : Function.Injective j.left.appTop)
    (h : j ≫ f = j ≫ g) : f = g := by
  let e := equalizer.ι f g
  have hfac : equalizer.lift j h ≫ e = j := equalizer.lift_ι _ _
  have hinj : Function.Injective e.left.appTop := by
    have hcomp : j.left.appTop = e.left.appTop ≫ (equalizer.lift j h).left.appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, hfac]
    intro x y hxy
    apply hj
    rw [hcomp, CommRingCat.comp_apply, CommRingCat.comp_apply, hxy]
  have : IsIso e.left := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  have : IsIso e := (isIso_iff_of_reflects_iso e (Over.forget S)).mp this
  rw [← cancel_epi e]
  exact equalizer.condition f g

section Algebra

variable (k : Type u) [Field k]

/-- The ideal of the origin of the affine line over `k`. -/
abbrev originIdeal : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance originIdeal_isPrime : (originIdeal k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- The local ring `k[s]_(s)` of the affine line at the origin. -/
abbrev LocalLine : Type u := Localization.AtPrime (originIdeal k)

/-- The fraction field `k(s)` of the local ring at the origin. -/
abbrev LocalLineFrac : Type u := FractionRing (LocalLine k)

/-- The coordinate `s` of the local ring at the origin. -/
def coord : LocalLine k := algebraMap (Polynomial k) (LocalLine k) Polynomial.X

theorem originIdeal_ne_bot : originIdeal k ≠ ⊥ := by
  simp [Polynomial.X_ne_zero]

instance : IsDiscreteValuationRing (LocalLine k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k)
    (originIdeal_ne_bot k) _

theorem coord_irreducible : Irreducible (coord k) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal (originIdeal k), Ideal.map_span,
    Set.image_singleton]
  rfl

variable {k}

theorem mem_originIdeal_iff (g : Polynomial k) : g ∈ originIdeal k ↔ g.coeff 0 = 0 := by
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]

/-- Evaluate the local ring at an element where every polynomial prime to `s` is a unit. -/
def evalAt {B : Type u} [CommRing B] [Algebra k B] (w : B)
    (hw : ∀ g : Polynomial k, g.coeff 0 ≠ 0 → IsUnit (Polynomial.aeval w g)) :
    LocalLine k →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := (originIdeal k).primeCompl) (f := Polynomial.aeval w)
    (fun g => hw g fun h0 => g.2 ((mem_originIdeal_iff (g : Polynomial k)).mpr h0))

@[simp]
theorem evalAt_coord {B : Type u} [CommRing B] [Algebra k B] (w : B)
    (hw : ∀ g : Polynomial k, g.coeff 0 ≠ 0 → IsUnit (Polynomial.aeval w g)) :
    evalAt w hw (coord k) = w := by
  simp [evalAt, coord, IsLocalization.lift_eq]

/-- Two `k`-algebra maps out of the local ring agree when they agree on `s`. -/
theorem algHom_ext {B : Type u} [CommRing B] [Algebra k B] {f g : LocalLine k →ₐ[k] B}
    (h : f (coord k) = g (coord k)) : f = g := by
  have hp : f.comp (IsScalarTower.toAlgHom k (Polynomial k) (LocalLine k)) =
      g.comp (IsScalarTower.toAlgHom k (Polynomial k) (LocalLine k)) :=
    Polynomial.algHom_ext h
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (originIdeal k).primeCompl
  exact congrArg AlgHom.toRingHom hp

/-- Evaluation at the origin. -/
def evalZero : LocalLine k →ₐ[k] k :=
  evalAt 0 fun g hg => by
    rw [← Polynomial.coeff_zero_eq_aeval_zero]
    exact hg.isUnit

@[simp]
theorem evalZero_coord : evalZero (coord k) = 0 := evalAt_coord _ _

theorem evalZero_surjective : Function.Surjective (evalZero (k := k)) :=
  fun c => ⟨algebraMap k (LocalLine k) c, AlgHom.commutes _ c⟩

/-- The residue field of `k[s]_(s)` is geometrically reduced over `k`. -/
theorem isGeometricallyReduced_residueField :
    Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField (LocalLine k)) := by
  have : IsLocalHom (evalZero (k := k)).toRingHom :=
    IsLocalHom.of_surjective _ evalZero_surjective
  have : Algebra.IsGeometricallyReduced k k := by
    rw [Algebra.isGeometricallyReduced_field_iff]
    exact isReduced_of_injective (Algebra.TensorProduct.rid k k (AlgebraicClosure k))
      (Algebra.TensorProduct.rid k k (AlgebraicClosure k)).injective
  let f : IsLocalRing.ResidueField (LocalLine k) →ₐ[k] k :=
    { IsLocalRing.ResidueField.lift (evalZero (k := k)).toRingHom with
      commutes' := fun c => by
        simp [IsScalarTower.algebraMap_apply k (LocalLine k)
          (IsLocalRing.ResidueField (LocalLine k))] }
  exact Algebra.IsGeometricallyReduced.of_injective f (RingHom.injective _)

/-- A map out of the local ring extends to its fraction field when `s` becomes a unit. -/
def fracLift {B : Type u} [CommRing B] [Algebra k B] (f : LocalLine k →ₐ[k] B)
    (hf : IsUnit (f (coord k))) : LocalLineFrac k →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (LocalLine k)) (f := f) fun y => by
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero y.2) (coord_irreducible k)
    rw [hv, map_mul, map_pow]
    exact (v.isUnit.map f).mul (hf.pow n)

theorem fracLift_comp {B : Type u} [CommRing B] [Algebra k B] (f : LocalLine k →ₐ[k] B)
    (hf : IsUnit (f (coord k))) :
    (fracLift f hf).comp (IsScalarTower.toAlgHom k (LocalLine k) (LocalLineFrac k)) = f :=
  AlgHom.ext fun r => IsLocalization.lift_eq _ r

end Algebra

section PowerSeries

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]

/-- The constant coefficient as a `k`-algebra map. -/
def constantCoeffAlg : PowerSeries A →ₐ[k] A :=
  { (PowerSeries.constantCoeff : PowerSeries A →+* A) with
    commutes' := fun c => by simp [PowerSeries.algebraMap_apply] }

@[simp]
theorem constantCoeffAlg_apply (f : PowerSeries A) :
    constantCoeffAlg (k := k) f = PowerSeries.constantCoeff f := rfl

theorem isUnit_aeval_of_constantCoeff {w : PowerSeries A}
    (hw : PowerSeries.constantCoeff w = 0) (g : Polynomial k) (hg : g.coeff 0 ≠ 0) :
    IsUnit (Polynomial.aeval w g) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have : PowerSeries.constantCoeff (Polynomial.aeval w g) = algebraMap k A (g.coeff 0) := by
    rw [← constantCoeffAlg_apply (k := k), ← Polynomial.aeval_algHom_apply,
      constantCoeffAlg_apply, hw, ← Polynomial.coeff_zero_eq_aeval_zero']
  rw [this]
  exact hg.isUnit.map _

/-- Substitute a power series without constant term for `s`. -/
def psEval (w : PowerSeries A) (hw : PowerSeries.constantCoeff w = 0) :
    LocalLine k →ₐ[k] PowerSeries A :=
  evalAt w (isUnit_aeval_of_constantCoeff hw)

theorem constantCoeffAlg_comp_psEval (w : PowerSeries A)
    (hw : PowerSeries.constantCoeff w = 0) :
    (constantCoeffAlg (k := k)).comp (psEval w hw) = (Algebra.ofId k A).comp evalZero :=
  algHom_ext (by simp [psEval, hw])

theorem constantCoeffAlg_comp_C :
    (constantCoeffAlg (k := k)).comp (IsScalarTower.toAlgHom k A (PowerSeries A)) =
      AlgHom.id k A :=
  AlgHom.ext fun c => by simp [PowerSeries.algebraMap_eq]

/-- The Laurent-type localization `A⟦X⟧[1/X]`. -/
abbrev PSLoc (A : Type u) [CommRing A] := Localization.Away (PowerSeries.X : PowerSeries A)

/-- The localization map `A⟦X⟧ → A⟦X⟧[1/X]`. -/
abbrev psLoc : PowerSeries A →ₐ[k] PSLoc A :=
  IsScalarTower.toAlgHom k (PowerSeries A) (PSLoc A)

theorem psLoc_injective : Function.Injective (psLoc (k := k) (A := A)) := by
  refine IsLocalization.injective (M := Submonoid.powers (PowerSeries.X : PowerSeries A))
    (PSLoc A) ?_
  rw [Submonoid.powers_le]
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro z hz
    exact PowerSeries.X_mul_cancel (by rw [hz, mul_zero])
  · intro z hz
    exact PowerSeries.mul_X_cancel (by rw [hz, zero_mul])

theorem isUnit_psLoc_X : IsUnit (psLoc (k := k) (PowerSeries.X : PowerSeries A)) :=
  IsLocalization.Away.algebraMap_isUnit _

/-- The point `s ↦ w` of `k(s)` with values in `A⟦X⟧[1/X]`. -/
def laurentPoint (w : PowerSeries A) (hw0 : PowerSeries.constantCoeff w = 0)
    (hw : IsUnit (psLoc (k := k) w)) : LocalLineFrac k →ₐ[k] PSLoc A :=
  fracLift ((psLoc (k := k)).comp (psEval w hw0)) (by simpa [psEval] using hw)

theorem laurentPoint_comp (w : PowerSeries A) (hw0 : PowerSeries.constantCoeff w = 0)
    (hw : IsUnit (psLoc (k := k) w)) :
    (laurentPoint w hw0 hw).comp (IsScalarTower.toAlgHom k (LocalLine k) (LocalLineFrac k)) =
      (psLoc (k := k)).comp (psEval w hw0) :=
  fracLift_comp _ _

theorem laurentPoint_coord (w : PowerSeries A) (hw0 : PowerSeries.constantCoeff w = 0)
    (hw : IsUnit (psLoc (k := k) w)) :
    laurentPoint w hw0 hw (algebraMap (LocalLine k) (LocalLineFrac k) (coord k)) =
      psLoc (k := k) w := by
  have := congrArg (fun f => f (coord k)) (laurentPoint_comp w hw0 hw)
  simpa [psEval] using this

end PowerSeries

section Scheme

open PseudoComplete

variable {k : Type u} [Field k]

/-- The relative spectrum of a map of `k`-algebras. -/
def specMap {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (f : A →ₐ[k] A') : algebraSpec k A' ⟶ algebraSpec k A :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op

theorem specMap_comp {A A' A'' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] [CommRing A''] [Algebra k A''] (f : A →ₐ[k] A') (g : A' →ₐ[k] A'') :
    specMap (g.comp f) = specMap g ≫ specMap f := by
  show (algSpec (CommRingCat.of k)).map ((CommAlgCat.ofHom f ≫ CommAlgCat.ofHom g).op) = _
  rw [op_comp, Functor.map_comp]
  rfl

theorem specMap_id (A : Type u) [CommRing A] [Algebra k A] :
    specMap (AlgHom.id k A) = 𝟙 _ :=
  (algSpec (CommRingCat.of k)).map_id _

theorem genericPoint_eq_specMap :
    genericPoint (k := k) (LocalLine k) =
      specMap (IsScalarTower.toAlgHom k (LocalLine k) (LocalLineFrac k)) := rfl

theorem specMap_left {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (f : A →ₐ[k] A') : (specMap f).left = Spec.map (CommRingCat.ofHom (f : A →+* A')) := rfl

instance isAffine_algebraSpec_left (A : Type u) [CommRing A] [Algebra k A] :
    IsAffine (algebraSpec k A).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

/-- Global sections of a relative spectrum map are the algebra map. -/
theorem ΓSpecIso_specMap_appTop {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] (f : A →ₐ[k] A') (x : Γ((algebraSpec k A).left, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of A')).hom ((specMap f).left.appTop x) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x) := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* A'))
  exact congrArg (fun g => CommRingCat.Hom.hom g x) e

theorem specMap_appTop_injective {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] (f : A →ₐ[k] A') (hf : Function.Injective f) :
    Function.Injective (specMap f).left.appTop := by
  intro x y hxy
  have h1 := ΓSpecIso_specMap_appTop f x
  rw [hxy, ΓSpecIso_specMap_appTop] at h1
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective (hf h1).symm

theorem specMap_psLoc_comp {A : Type u} [CommRing A] [Algebra k A] (w : PowerSeries A)
    (hw0 : PowerSeries.constantCoeff w = 0) (hw : IsUnit (psLoc (k := k) w)) :
    specMap (psLoc (k := k) (A := A)) ≫ specMap (psEval w hw0) =
      specMap (laurentPoint w hw0 hw) ≫ genericPoint (k := k) (LocalLine k) := by
  rw [← specMap_comp, ← laurentPoint_comp w hw0 hw, specMap_comp]
  rfl

theorem algebraSpec_self_hom_isIso : IsIso (algebraSpec k k).hom := by
  rw [algebraSpec_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  exact IsIso.id _

/-- Morphisms into the relative spectrum of the ground field are unique. -/
theorem algebraSpec_self_ext {T : Over (Spec (CommRingCat.of k))}
    (f g : T ⟶ algebraSpec k k) : f = g := by
  have := algebraSpec_self_hom_isIso (k := k)
  apply Over.OverMorphism.ext
  rw [← cancel_mono (algebraSpec k k).hom, Over.w f, Over.w g]

/-- The structure map of the relative spectrum of `k` is the identity. -/
def pointOfSpec : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ algebraSpec k k :=
  Over.homMk (𝟙 _) (by
    rw [algebraSpec_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp _)

/-- Morphisms out of a `k`-scheme agree when they agree on every affine test. -/
theorem hom_ext_of_algebraSpec {T Y : Over (Spec (CommRingCat.of k))} {f g : T ⟶ Y}
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A] (c : algebraSpec k A ⟶ T),
      c ≫ f = c ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineOpenCover.openCover _ _ fun j => ?_
  let : Algebra k (T.left.affineOpenCover.X j) :=
    (Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)).hom.toAlgebra
  let c : algebraSpec k (T.left.affineOpenCover.X j) ⟶ T :=
    Over.homMk (T.left.affineOpenCover.f j) (by
      rw [algebraSpec_hom]
      exact (Spec.map_preimage _).symm)
  exact congrArg CommaMorphism.left (h _ c)

variable {H V : GroupScheme (Spec (CommRingCat.of k))} {X : Over (Spec (CommRingCat.of k))}

/-- The comparison over `A⟦X⟧`: when the translate of the `X`-point by `q(h)` is the
`w`-point on `A⟦X⟧[1/X]`, the action of `h` fixes the specialization at the origin. -/
theorem act_eq_of_laurent (a : SchemeAction H X) [IsSeparated X.hom] (q : H ⟶ V)
    (ρ : V.X ⟶ X)
    (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X),
      a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ)
    (vK : algebraSpec k (LocalLineFrac k) ⟶ V.X) (φ : algebraSpec k (LocalLine k) ⟶ X)
    (hφ : genericPoint (LocalLine k) ≫ φ = vK ≫ ρ)
    {A : Type u} [CommRing A] [Algebra k A] (h : algebraSpec k A ⟶ H.X)
    (w : PowerSeries A) (hw0 : PowerSeries.constantCoeff w = 0)
    (hw : IsUnit (psLoc (k := k) w))
    (heq : (specMap ((psLoc (k := k)).comp (IsScalarTower.toAlgHom k A (PowerSeries A))) ≫
          h ≫ q.hom.hom) *
        (specMap (laurentPoint PowerSeries.X PowerSeries.constantCoeff_X isUnit_psLoc_X) ≫ vK) =
      specMap (laurentPoint w hw0 hw) ≫ vK) :
    a.act h (specMap ((Algebra.ofId k A).comp evalZero) ≫ φ) =
      specMap ((Algebra.ofId k A).comp evalZero) ≫ φ := by
  have key : a.act (specMap (IsScalarTower.toAlgHom k A (PowerSeries A)) ≫ h)
      (specMap (psEval PowerSeries.X PowerSeries.constantCoeff_X) ≫ φ) =
      specMap (psEval w hw0) ≫ φ := by
    refine OrbitLimit.ext_of_injective_appTop _ _ (specMap (psLoc (k := k) (A := A)))
      (specMap_appTop_injective _ psLoc_injective) ?_
    have e1 : specMap (psLoc (k := k) (A := A)) ≫
        specMap (psEval (k := k) (A := A) PowerSeries.X PowerSeries.constantCoeff_X) ≫ φ =
        (specMap (laurentPoint (k := k) (A := A) PowerSeries.X PowerSeries.constantCoeff_X
          isUnit_psLoc_X) ≫ vK) ≫ ρ := by
      rw [← Category.assoc, specMap_psLoc_comp (A := A) PowerSeries.X
        PowerSeries.constantCoeff_X isUnit_psLoc_X, Category.assoc, hφ, Category.assoc]
    have e2 : specMap (psLoc (k := k) (A := A)) ≫
        specMap (IsScalarTower.toAlgHom k A (PowerSeries A)) ≫ h =
        specMap ((psLoc (k := k)).comp (IsScalarTower.toAlgHom k A (PowerSeries A))) ≫ h := by
      rw [specMap_comp, Category.assoc]
    have e3 : specMap (psLoc (k := k) (A := A)) ≫ specMap (psEval w hw0) ≫ φ =
        (specMap (laurentPoint w hw0 hw) ≫ vK) ≫ ρ := by
      rw [← Category.assoc, specMap_psLoc_comp w hw0 hw, Category.assoc, hφ, Category.assoc]
    rw [a.naturality, e1, e2, e3, hρ]
    have heq' := congrArg (· ≫ ρ) heq
    simp only [Category.assoc] at heq' ⊢
    exact heq'
  have f1 : specMap (constantCoeffAlg (k := k) (A := A)) ≫
      specMap (IsScalarTower.toAlgHom k A (PowerSeries A)) ≫ h = h := by
    rw [← Category.assoc, ← specMap_comp, constantCoeffAlg_comp_C, specMap_id]
    exact Category.id_comp h
  have f2 : ∀ (w : PowerSeries A) (hw0 : PowerSeries.constantCoeff w = 0),
      specMap (constantCoeffAlg (k := k) (A := A)) ≫ specMap (psEval w hw0) ≫ φ =
        specMap ((Algebra.ofId k A).comp evalZero) ≫ φ := by
    intro w hw0
    rw [← Category.assoc, ← specMap_comp, constantCoeffAlg_comp_psEval]
  have h2 := congrArg (fun f => specMap (constantCoeffAlg (k := k) (A := A)) ≫ f) key
  rwa [a.naturality, f1, f2, f2] at h2

/-- If every affine translate is detected by a power series `w`, the specialization at the
origin of the extended `k(s)`-orbit point is a fixed rational point. -/
theorem exists_isFixed_of_laurent (a : SchemeAction H X) (hX : IsPseudoComplete X)
    (q : H ⟶ V) (ρ : V.X ⟶ X)
    (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X),
      a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ)
    (vK : algebraSpec k (LocalLineFrac k) ⟶ V.X)
    (hw : ∀ (A : Type u) [CommRing A] [Algebra k A] (h : algebraSpec k A ⟶ H.X),
      ∃ (w : PowerSeries A) (hw0 : PowerSeries.constantCoeff w = 0)
        (hwu : IsUnit (psLoc (k := k) w)),
        (specMap ((psLoc (k := k)).comp (IsScalarTower.toAlgHom k A (PowerSeries A))) ≫
            h ≫ q.hom.hom) *
          (specMap (laurentPoint PowerSeries.X PowerSeries.constantCoeff_X isUnit_psLoc_X) ≫
            vK) =
        specMap (laurentPoint w hw0 hwu) ≫ vK) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y := by
  have := hX.isSeparated
  obtain ⟨φ, hφ⟩ := hX.exists_extension (LocalLine k) isGeometricallyReduced_residueField
    (vK ≫ ρ)
  refine ⟨pointOfSpec ≫ specMap evalZero ≫ φ, ?_⟩
  intro T b h
  apply hom_ext_of_algebraSpec
  intro A _ _ c
  have hy : c ≫ b ≫ pointOfSpec ≫ specMap evalZero ≫ φ =
      specMap ((Algebra.ofId k A).comp evalZero) ≫ φ := by
    rw [specMap_comp, algebraSpec_self_ext (specMap (Algebra.ofId k A)) (c ≫ b ≫ pointOfSpec)]
    simp only [Category.assoc]
  obtain ⟨w, hw0, hwu, heq⟩ := hw A (c ≫ h)
  rw [a.naturality, hy]
  exact act_eq_of_laurent a q ρ hρ vK φ hφ (c ≫ h) w hw0 hwu heq

/-- Global sections of the relative spectrum of `B`, identified with `B`. -/
def gammaIso (k : Type u) [Field k] (B : Type u) [CommRing B] [Algebra k B] :
    Γ((algebraSpec k B).left, ⊤) ≅ CommRingCat.of B :=
  Scheme.ΓSpecIso (CommRingCat.of B)

theorem algebraMap_coord_ne_zero :
    algebraMap (LocalLine k) (LocalLineFrac k) (coord k) ≠ 0 := by
  rw [Ne, ← map_zero (algebraMap (LocalLine k) (LocalLineFrac k))]
  exact fun h => (coord_irreducible k).ne_zero (IsFractionRing.injective _ _ h)

end Scheme

section Gm

variable {k : Type u} [Field k] {V : GroupScheme (Spec (CommRingCat.of k))}
  (eV : V ≅ (Gm (Spec (CommRingCat.of k))).toGrp)

open PseudoComplete

/-- The unit coordinate of an affine point of a group isomorphic to `𝔾_m`. -/
def gmCoord {B : Type u} [CommRing B] [Algebra k B] (v : algebraSpec k B ⟶ V.X) : Bˣ :=
  Units.map (gammaIso k B).hom.hom.toMonoidHom
    (Gm.pointsEquiv _ _ (v ≫ eV.hom.hom.hom))

/-- The affine point of a group isomorphic to `𝔾_m` with a given unit coordinate. -/
def gmPoint {B : Type u} [CommRing B] [Algebra k B] (t : Bˣ) : algebraSpec k B ⟶ V.X :=
  (Gm.pointsEquiv _ (algebraSpec k B)).symm
      (Units.map (gammaIso k B).inv.hom.toMonoidHom t) ≫
    eV.inv.hom.hom

theorem gmCoord_mul {B : Type u} [CommRing B] [Algebra k B] (v₁ v₂ : algebraSpec k B ⟶ V.X) :
    gmCoord eV (v₁ * v₂) = gmCoord eV v₁ * gmCoord eV v₂ := by
  rw [gmCoord, MonObj.mul_comp, Gm.pointsEquiv_mul, map_mul]
  rfl

theorem gmCoord_specMap {B B' : Type u} [CommRing B] [Algebra k B] [CommRing B'] [Algebra k B']
    (f : B →ₐ[k] B') (v : algebraSpec k B ⟶ V.X) :
    gmCoord eV (specMap f ≫ v) = Units.map (f : B →+* B').toMonoidHom (gmCoord eV v) := by
  apply Units.ext
  simp only [gmCoord, Category.assoc, Gm.pointsEquiv_naturality, Units.coe_map]
  exact ΓSpecIso_specMap_appTop f _

theorem gmCoord_injective {B : Type u} [CommRing B] [Algebra k B] :
    Function.Injective (gmCoord eV (B := B)) := by
  intro v₁ v₂ hv
  have h1 := Units.map_injective (gammaIso k B).commRingCatIsoToRingEquiv.injective hv
  have h2 := (Gm.pointsEquiv _ _).injective h1
  have h3 : eV.hom.hom.hom ≫ eV.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, eV.hom_inv_id, Grp.id_hom_hom]
  calc v₁ = v₁ ≫ eV.hom.hom.hom ≫ eV.inv.hom.hom := by rw [h3, Category.comp_id]
    _ = v₂ ≫ eV.hom.hom.hom ≫ eV.inv.hom.hom := by
      rw [← Category.assoc, h2, Category.assoc]
    _ = v₂ := by rw [h3, Category.comp_id]

theorem gmCoord_gmPoint {B : Type u} [CommRing B] [Algebra k B] (t : Bˣ) :
    gmCoord eV (gmPoint eV t) = t := by
  have h3 : eV.inv.hom.hom ≫ eV.hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, eV.inv_hom_id, Grp.id_hom_hom]
  rw [gmCoord, gmPoint, Category.assoc, h3, Category.comp_id, MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [Units.coe_map, Units.coe_map]
  exact CommRingCat.hom_inv_apply _ _

include eV in
/-- The `𝔾_m` case: the translates of `s` are the power series `c X`. -/
theorem exists_isFixed_of_gm {H : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction H X) (hX : IsPseudoComplete X)
    (q : H ⟶ V) (ρ : V.X ⟶ X)
    (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X),
      a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y := by
  let sK := algebraMap (LocalLine k) (LocalLineFrac k) (coord k)
  have hs : sK ≠ 0 := algebraMap_coord_ne_zero
  refine exists_isFixed_of_laurent a hX q ρ hρ (gmPoint eV (Units.mk0 sK hs)) ?_
  intro A _ _ h
  let c := gmCoord eV (h ≫ q.hom.hom)
  let w : PowerSeries A := algebraMap A (PowerSeries A) c * PowerSeries.X
  have hw0 : PowerSeries.constantCoeff w = 0 := by simp [w]
  have hwu : IsUnit (psLoc (k := k) w) := by
    rw [map_mul]
    exact ((c.isUnit.map (algebraMap A (PowerSeries A))).map psLoc).mul isUnit_psLoc_X
  refine ⟨w, hw0, hwu, gmCoord_injective eV ?_⟩
  rw [gmCoord_mul, gmCoord_specMap, gmCoord_specMap, gmCoord_specMap, gmCoord_gmPoint]
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, Units.val_mk0]
  change psLoc (k := k) (algebraMap A (PowerSeries A) c) *
      laurentPoint (k := k) (A := A) PowerSeries.X PowerSeries.constantCoeff_X isUnit_psLoc_X sK =
    laurentPoint (k := k) (A := A) w hw0 hwu sK
  rw [laurentPoint_coord, laurentPoint_coord, ← map_mul]

end Gm

section Ga

variable {k : Type u} [Field k] {V : GroupScheme (Spec (CommRingCat.of k))}
  (e : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))

open PseudoComplete

/-- The additive coordinate of an affine point of a one-dimensional vector group. -/
def gaCoord {B : Type u} [CommRing B] [Algebra k B] (v : algebraSpec k B ⟶ V.X) : B :=
  (gammaIso k B).hom ((e _ v).toAdd 0)

/-- The affine point of a one-dimensional vector group with a given coordinate. -/
def gaPoint {B : Type u} [CommRing B] [Algebra k B] (t : B) : algebraSpec k B ⟶ V.X :=
  (e _).symm (Multiplicative.ofAdd fun _ => (gammaIso k B).inv t)

theorem gaCoord_mul {B : Type u} [CommRing B] [Algebra k B] (v₁ v₂ : algebraSpec k B ⟶ V.X) :
    gaCoord e (v₁ * v₂) = gaCoord e v₁ + gaCoord e v₂ := by
  rw [gaCoord, map_mul, toAdd_mul, Pi.add_apply, map_add]
  rfl

theorem gaCoord_specMap
    (he : ∀ (T V' : Over (Spec (CommRingCat.of k))) (b : V' ⟶ T) (x : T ⟶ V.X),
      (e V' (b ≫ x)).toAdd = fun j => b.left.appTop ((e T x).toAdd j))
    {B B' : Type u} [CommRing B] [Algebra k B] [CommRing B'] [Algebra k B']
    (f : B →ₐ[k] B') (v : algebraSpec k B ⟶ V.X) :
    gaCoord e (specMap f ≫ v) = f (gaCoord e v) := by
  rw [gaCoord, he]
  exact ΓSpecIso_specMap_appTop f _

theorem gaCoord_injective {B : Type u} [CommRing B] [Algebra k B] :
    Function.Injective (gaCoord e (B := B)) := by
  intro v₁ v₂ hv
  apply (e _).injective
  apply Multiplicative.toAdd.injective
  funext j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  exact (gammaIso k B).commRingCatIsoToRingEquiv.injective hv

theorem gaCoord_gaPoint {B : Type u} [CommRing B] [Algebra k B] (t : B) :
    gaCoord e (gaPoint e t) = t := by
  rw [gaCoord, gaPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  exact CommRingCat.hom_inv_apply _ _

/-- The `𝔾_a` case: the translates of `1 / s` are `1 / w` with `w = X / (1 + c X)`. -/
theorem exists_isFixed_of_ga {H : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction H X) (hX : IsPseudoComplete X)
    (q : H ⟶ V) (ρ : V.X ⟶ X)
    (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X),
      a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ)
    (he : ∀ (T V' : Over (Spec (CommRingCat.of k))) (b : V' ⟶ T) (x : T ⟶ V.X),
      (e V' (b ≫ x)).toAdd = fun j => b.left.appTop ((e T x).toAdd j)) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y := by
  let sK := algebraMap (LocalLine k) (LocalLineFrac k) (coord k)
  have hs : sK ≠ 0 := algebraMap_coord_ne_zero
  refine exists_isFixed_of_laurent a hX q ρ hρ (gaPoint e sK⁻¹) ?_
  intro A _ _ h
  let c := gaCoord e (h ≫ q.hom.hom)
  have hu : IsUnit (1 + algebraMap A (PowerSeries A) c * PowerSeries.X) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  let u := hu.unit
  let w : PowerSeries A := (PowerSeries.X : PowerSeries A) * ↑u⁻¹
  have hw0 : PowerSeries.constantCoeff w = 0 := by simp [w]
  have hwu : IsUnit (psLoc (k := k) w) := by
    rw [map_mul]
    exact isUnit_psLoc_X.mul (u⁻¹.isUnit.map _)
  refine ⟨w, hw0, hwu, gaCoord_injective e ?_⟩
  rw [gaCoord_mul, gaCoord_specMap e he, gaCoord_specMap e he, gaCoord_specMap e he,
    gaCoord_gaPoint]
  change psLoc (k := k) (algebraMap A (PowerSeries A) c) +
      laurentPoint (k := k) (A := A) PowerSeries.X PowerSeries.constantCoeff_X isUnit_psLoc_X
        sK⁻¹ =
    laurentPoint (k := k) (A := A) w hw0 hwu sK⁻¹
  have hX : psLoc (k := k) (PowerSeries.X : PowerSeries A) *
      laurentPoint (k := k) (A := A) PowerSeries.X PowerSeries.constantCoeff_X isUnit_psLoc_X
        sK⁻¹ = 1 := by
    rw [← laurentPoint_coord (k := k) (A := A) PowerSeries.X PowerSeries.constantCoeff_X
      isUnit_psLoc_X, ← map_mul, mul_inv_cancel₀ hs, map_one]
  have hW : psLoc (k := k) w * laurentPoint (k := k) (A := A) w hw0 hwu sK⁻¹ = 1 := by
    rw [← laurentPoint_coord (k := k) (A := A) w hw0 hwu, ← map_mul, mul_inv_cancel₀ hs,
      map_one]
  have hu' : (1 + psLoc (k := k) (algebraMap A (PowerSeries A) c) *
      psLoc (k := k) (PowerSeries.X : PowerSeries A)) * psLoc (k := k) (↑u⁻¹ : PowerSeries A) =
      1 := by
    have := congrArg (psLoc (k := k)) u.mul_inv
    rwa [map_mul, IsUnit.unit_spec, map_add, map_one, map_mul] at this
  replace hW : psLoc (k := k) (PowerSeries.X : PowerSeries A) *
      psLoc (k := k) (↑u⁻¹ : PowerSeries A) *
      laurentPoint (k := k) (A := A) w hw0 hwu sK⁻¹ = 1 := by
    rw [← map_mul]
    exact hW
  linear_combination (-psLoc (k := k) (algebraMap A (PowerSeries A) c) +
      (1 + psLoc (k := k) (algebraMap A (PowerSeries A) c) *
        psLoc (k := k) (PowerSeries.X : PowerSeries A)) *
        psLoc (k := k) (↑u⁻¹ : PowerSeries A) *
        laurentPoint (k := k) (A := A) w hw0 hwu sK⁻¹) * hX -
    (1 + psLoc (k := k) (algebraMap A (PowerSeries A) c) *
      psLoc (k := k) (PowerSeries.X : PowerSeries A)) *
      laurentPoint (k := k) (A := A) PowerSeries.X PowerSeries.constantCoeff_X isUnit_psLoc_X
        sK⁻¹ * hW +
    laurentPoint (k := k) (A := A) w hw0 hwu sK⁻¹ * hu'

end Ga

end OrbitLimit

namespace SchemeAction

variable {k : Type u} [Field k] {H V : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))}

/-- An action on a pseudo-complete scheme has a fixed rational point as soon as there is an
equivariant map from a group scheme `V` satisfying `IsElementaryQuotient` (a one-dimensional
vector group or `𝔾_m`), on which `H` acts by left translation through a morphism `q : H ⟶ V`. -/
theorem exists_isFixed_of_elementary_equivariant (a : SchemeAction H X)
    (hX : IsPseudoComplete X) (q : H ⟶ V)
    (hV : SplitSolvable.IsElementaryQuotient V) (ρ : V.X ⟶ X)
    (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ V.X),
      a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y := by
  rcases hV with ⟨e, he⟩ | hV
  · exact OrbitLimit.exists_isFixed_of_ga e a hX q ρ hρ he
  · obtain ⟨eV⟩ := hV
    exact OrbitLimit.exists_isFixed_of_gm eV a hX q ρ hρ

end SchemeAction

end Langlands.GroupScheme
