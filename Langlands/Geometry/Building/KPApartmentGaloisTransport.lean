import Langlands.Geometry.Building.RootDatumValuationGaloisAction
import Langlands.Geometry.Building.GaloisApartmentQuotientAction

/-! # Coefficient covariance and split-torus compatibility -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.characterLattice

/-- Evaluation of a transported character after a specified descent equality. -/
theorem points_of_descent_eq {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (T : CommGroupScheme B)
    (χ χ' : characterLattice ((CommGroupScheme.baseChange b).obj T))
    (U : Over S) (c : (Over.map a).obj U ⟶ U)
    (x y : U ⟶ ((CommGroupScheme.baseChange b).obj T).X)
    (hx : descentPoint b a ha T.toGrp U x = c ≫ y)
    (hχ : Gm.pointsEquiv S U (x ≫ (CommGroupScheme.groupHom χ').hom.hom) =
      Gm.pointsEquiv S ((Over.map a).obj U)
        (descentPoint b a ha T.toGrp U x ≫ (CommGroupScheme.groupHom χ).hom.hom)) :
    Gm.pointsEquiv S U
        (x ≫ (CommGroupScheme.groupHom χ').hom.hom) =
      Units.map c.left.appTop.hom.toMonoidHom
        (Gm.pointsEquiv S U (y ≫ (CommGroupScheme.groupHom χ).hom.hom)) := by
  rw [hχ, hx, Category.assoc, Gm.pointsEquiv_naturality]

end Langlands.GroupScheme.characterLattice

namespace Langlands.GroupScheme

/-- An invariant function also removes an inverse change in its argument. -/
theorem invariant_apply_of_inverse {A B : Type*} (f g : A → A) (ω : A → B)
    (hfg : ∀ t, f (g t) = t) (hω : ∀ t, ω (f t) = ω t)
    {x y : A} (hxy : x = g y) : ω x = ω y := by
  calc
    ω x = ω (g y) := congrArg ω hxy
    _ = ω (f (g y)) := (hω _).symm
    _ = ω y := congrArg ω (hfg y)

/-- The unit maps of inverse algebra automorphisms cancel. -/
theorem units_map_algEquiv_inv {k L : Type*} [CommSemiring k] [Semiring L]
    [Algebra k L] (σ : L ≃ₐ[k] L) (t : Lˣ) :
    Units.map σ.toMonoidHom (Units.map σ⁻¹.toMonoidHom t) = t := by
  apply Units.ext
  exact σ.apply_symm_apply t

/-- Coefficient evaluation of a lattice character as global-unit evaluation. -/
theorem rationalCharacterEval_lattice {L : Type u} [Field L]
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (χ : characterLattice T) (s : rationalPoints T.toGrp) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ) s =
      Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.toMonoidHom
        (Gm.pointsEquiv _ _ (s ≫ (CommGroupScheme.groupHom χ).hom.hom)) := rfl

/-- Naturality of the global-section identification, restricted to units. -/
theorem units_ΓSpecIso_naturality {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (z : (Γ(Spec R, ⊤))ˣ) :
    Units.map (Scheme.ΓSpecIso R').hom.hom.toMonoidHom
        (Units.map (Spec.map f).appTop.hom.toMonoidHom z) =
      Units.map f.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom z) := by
  apply Units.ext
  change ((Spec.map f).appTop ≫ (Scheme.ΓSpecIso R').hom) _ =
    ((Scheme.ΓSpecIso R).hom ≫ f) _
  rw [Scheme.ΓSpecIso_naturality]

end Langlands.GroupScheme

namespace Langlands.GroupScheme.GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "T_K" =>
  CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T

/-- Evaluation of a simultaneously transported character and point is the
coefficient automorphism applied to the original unit. -/
theorem rationalCharacterEval_galois (σ : K ≃ₐ[k] K)
    (a : characterLattice T_K) (s : rationalPoints (T_K).toGrp) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm
        (characterLattice.galoisRepresentation k K T σ a))
      (rationalConjugate k K T.toGrp σ s) =
        Units.map σ.toMonoidHom
          (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm a) s) := by
  have h := characterLattice.points_of_descent_eq
    (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
    T a (characterLattice.galoisRepresentation k K T σ a)
    (Over.mk (𝟙 _)) (galoisIdentityTestIso k K σ).hom
    (rationalConjugate k K T.toGrp σ s) s
    (descentPoint_rationalConjugate k K T.toGrp σ s)
    (characterLattice.galoisRepresentation_points k K T σ a _
      (rationalConjugate k K T.toGrp σ s))
  exact (rationalCharacterEval_lattice T_K _ _).trans
    ((congrArg
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom) h).trans
      ((units_ΓSpecIso_naturality (CommRingCat.ofHom σ.toRingHom) _).trans
        (congrArg (Units.map σ.toMonoidHom)
          (rationalCharacterEval_lattice T_K a s).symm)))

/-- Invariance of a unit function removes the coefficient change in evaluation. -/
theorem rationalCharacterOmegaEval_galois (σ : K ≃ₐ[k] K)
    {ω : Kˣ → ℝ} (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t)
    (a : characterLattice T_K) (s : rationalPoints (T_K).toGrp) :
    ω (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm
        (characterLattice.galoisRepresentation k K T σ a))
      (rationalConjugate k K T.toGrp σ s)) =
      ω (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm a) s) := by
  exact (congrArg ω (rationalCharacterEval_galois k K T σ a s)).trans (hω _)

variable {T}
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual coefficient conjugation is natural for maps descended from the base. -/
theorem rationalConjugate_map (f : G ⟶ H) (σ : K ≃ₐ[k] K)
    (s : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K H σ
        (rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map f) s) =
      rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map f)
        (rationalConjugate k K G σ s) := by
  apply (baseChangeCoeffEquiv k K H).injective
  rw [baseChangeCoeffEquiv_rationalConjugate, baseChangeCoeffEquiv_map,
    baseChangeCoeffEquiv_map, baseChangeCoeffEquiv_rationalConjugate]
  exact DFunLike.congr_fun
    (G.affinePointsTarget_naturality f (CommAlgCat.ofHom σ.toAlgHom))
    (baseChangeCoeffEquiv k K G s)

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

section Transport

variable {L : Type u} [Field L]
  {S : CommGroupScheme (Spec (CommRingCat.of L))}
  {H : GroupScheme (Spec (CommRingCat.of L))} [IsAffineHom H.X.hom]

/-- Compatibility can be pulled back along covariant character and point maps. -/
theorem IsSplitTorusCompatible.pullbackTransport (j : S.toGrp ⟶ H)
    {ω : Lˣ → ℝ} {φ ψ : RootFunctionFamily S H}
    (hφ : IsSplitTorusCompatible j ω φ)
    (α : characterLattice S → characterLattice S)
    (β : rationalPoints H →* rationalPoints H)
    (torusMap : rationalPoints S.toGrp → rationalPoints S.toGrp)
    (hψ : ∀ a g, ψ a g = φ (α a) (β g))
    (hroots : ∀ a ∈ relativeRoots j, α a ∈ relativeRoots j)
    (hgroups : ∀ a g, g ∈ rootGroupPoints j a → β g ∈ rootGroupPoints j (α a))
    (hmap : ∀ s, β (rationalPoints.map j s) = rationalPoints.map j (torusMap s))
    (hω : ∀ a s,
      ω (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm (α a))
        (torusMap s)) =
      ω (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s)) :
    IsSplitTorusCompatible j ω ψ := by
  intro a ha s g hg
  have h := hφ (α a) (hroots a ha) (torusMap s) (β g) (hgroups a g hg)
  rw [hω] at h
  simpa only [hψ, map_mul, map_inv, hmap] using h

end Transport

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

variable [IsAffineHom G.X.hom]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

omit [IsAffineHom G.X.hom] in
/-- The inverse family action uses the forward character and point maps. -/
theorem RootFunctionFamily.galoisAction_inv_apply (σ : K ≃ₐ[k] K)
    (φ : RootFunctionFamily T_K G_K) (a : characterLattice T_K)
    (g : rationalPoints G_K) :
    galoisAction k K T G σ⁻¹ φ a g =
      φ (characterLattice.galoisRepresentation k K T σ a)
        (rationalConjugate k K G σ g) := by
  rw [galoisAction_apply, inv_inv]

/-- Split-torus compatibility survives coefficient transport when the supplied
unit function is invariant under that automorphism. -/
theorem IsSplitTorusCompatible.galoisTransport_inv (σ : K ≃ₐ[k] K)
    {ω : Kˣ → ℝ} (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t)
    {φ : RootFunctionFamily T_K G_K}
    (hφ : IsSplitTorusCompatible (S := T_K) i_K ω φ) :
    IsSplitTorusCompatible (S := T_K) i_K ω
      (RootFunctionFamily.galoisAction k K T G σ⁻¹ φ) := by
  exact IsSplitTorusCompatible.pullbackTransport (S := T_K) (H := G_K)
    (φ := φ) (ψ := RootFunctionFamily.galoisAction k K T G σ⁻¹ φ)
    i_K hφ (characterLattice.galoisRepresentation k K T σ)
    (rationalConjugate k K G σ).toMonoidHom
    (rationalConjugate k K T.toGrp σ)
    (RootFunctionFamily.galoisAction_inv_apply k K σ φ)
    (fun a ha => (mem_roots_galois_iff k K i σ a).2 ha)
    (fun a u hu =>
      (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ a u).2 hu)
    (rationalConjugate_map k K i σ)
    (rationalCharacterOmegaEval_galois k K T σ hω)

/-- Split-torus compatibility is preserved by the original family action. -/
theorem IsSplitTorusCompatible.galoisTransport (σ : K ≃ₐ[k] K)
    {ω : Kˣ → ℝ} (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t)
    {φ : RootFunctionFamily T_K G_K}
    (hφ : IsSplitTorusCompatible (S := T_K) i_K ω φ) :
    IsSplitTorusCompatible (S := T_K) i_K ω
      (RootFunctionFamily.galoisAction k K T G σ φ) := by
  have hωinv (t : Kˣ) : ω (Units.map σ⁻¹.toMonoidHom t) = ω t :=
    invariant_apply_of_inverse
      (Units.map σ.toMonoidHom) (Units.map σ⁻¹.toMonoidHom) ω
      (units_map_algEquiv_inv σ) hω rfl
  simpa only [inv_inv] using
    IsSplitTorusCompatible.galoisTransport_inv k K i σ⁻¹ hωinv hφ

/-- The coefficient permutation restricts to exactly all split-torus-compatible
families for an invariant unit function. -/
def IsSplitTorusCompatible.galoisEquiv (σ : K ≃ₐ[k] K)
    {ω : Kˣ → ℝ} (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) :
    Equiv.Perm {φ : RootFunctionFamily T_K G_K //
      IsSplitTorusCompatible (S := T_K) i_K ω φ} where
  toFun φ := ⟨RootFunctionFamily.galoisAction k K T G σ φ.val,
    IsSplitTorusCompatible.galoisTransport k K i σ hω φ.property⟩
  invFun φ := ⟨RootFunctionFamily.galoisAction k K T G σ⁻¹ φ.val,
    IsSplitTorusCompatible.galoisTransport_inv k K i σ hω φ.property⟩
  left_inv φ := by
    apply Subtype.ext
    change (RootFunctionFamily.galoisAction k K T G σ⁻¹ *
      RootFunctionFamily.galoisAction k K T G σ) φ.val = φ.val
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv φ := by
    apply Subtype.ext
    change (RootFunctionFamily.galoisAction k K T G σ *
      RootFunctionFamily.galoisAction k K T G σ⁻¹) φ.val = φ.val
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

@[simp] theorem IsSplitTorusCompatible.galoisEquiv_val (σ : K ≃ₐ[k] K)
    {ω : Kˣ → ℝ} (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t)
    (φ : {φ : RootFunctionFamily T_K G_K //
      IsSplitTorusCompatible (S := T_K) i_K ω φ}) :
    (IsSplitTorusCompatible.galoisEquiv k K i σ hω φ).val =
      RootFunctionFamily.galoisAction k K T G σ φ.val := rfl

end Langlands.Geometry.Building
