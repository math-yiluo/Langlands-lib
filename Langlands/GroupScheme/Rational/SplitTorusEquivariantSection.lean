import Langlands.GroupScheme.Rational.SplitTorusVectorExtension

/-! # Equivariant scheme sections of torus-equivariant extensions by vector groups

A split torus acts compatibly on a group scheme `E`, on a quotient `q : E ⟶ H`, and on the
kernel `N`, a vector group with linear coordinates. A section of `q` as a morphism of schemes
can then be corrected to a torus-equivariant section of schemes. The correction is the
exponent-zero Laurent coefficient of the equivariance defect against the universal torus
point.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme

namespace splitTorus

open RelativeRoot PointedCoordinateWeights

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]

local notation "𝔻" => splitTorus (Spec (CommRingCat.of k)) I

omit [DecidableEq I] in
/-- Points of a split torus commute. -/
theorem points_mul_comm {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ (𝔻).X) :
    t * r = r * t := by
  apply (pointsEquiv I T).injective
  rw [map_mul, map_mul, mul_comm]

variable {E H N : GroupScheme (Spec (CommRingCat.of k))}
    (cE : AutomorphicAction (splitTorus (Spec (CommRingCat.of k)) I) E)
    (cH : AutomorphicAction (splitTorus (Spec (CommRingCat.of k)) I) H)
    (cN : AutomorphicAction (splitTorus (Spec (CommRingCat.of k)) I) N)
    (i : N ⟶ E) [Mono i.hom.hom] (q : E ⟶ H)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (hq : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (g : T ⟶ E.X),
      cE.act t g ≫ q.hom.hom = cH.act t (g ≫ q.hom.hom))
    (hi : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (w : T ⟶ N.X),
      cE.act t (w ≫ i.hom.hom) = cN.act t w ≫ i.hom.hom)
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 _)
    {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-- The equivariance defect of the scheme section on the universal pair. -/
def actionDefectUniversal : (𝔻).X ⊗ H.X ⟶ E.X :=
  cE.act (fst (𝔻).X H.X) (snd (𝔻).X H.X ≫ s) *
    (cH.act (fst (𝔻).X H.X) (snd (𝔻).X H.X) ≫ s)⁻¹

omit [DecidableEq I] [Mono i.hom.hom] in
include hker hq hs in
theorem actionDefectUniversal_mem :
    actionDefectUniversal I cE cH s ∈ (SubgroupFunctor.range i).carrier ((𝔻).X ⊗ H.X) := by
  rw [hker, actionDefectUniversal, MonObj.mul_comp, GrpObj.inv_comp, hq]
  simp only [Category.assoc, hs, Category.comp_id, mul_inv_cancel]

/-- The equivariance defect, as an actual morphism to the kernel. -/
def kernelActionDefect : (𝔻).X ⊗ H.X ⟶ N.X :=
  Classical.choose (actionDefectUniversal_mem I cE cH i q hker hq s hs)

omit [DecidableEq I] [Mono i.hom.hom] in
theorem kernelActionDefect_comp :
    kernelActionDefect I cE cH i q hker hq s hs ≫ i.hom.hom = actionDefectUniversal I cE cH s :=
  Classical.choose_spec (actionDefectUniversal_mem I cE cH i q hker hq s hs)

/-- The equivariance defect at a torus point and a point of the quotient. -/
def actionDefect {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ (𝔻).X) (x : T ⟶ H.X) :
    T ⟶ N.X :=
  lift t x ≫ kernelActionDefect I cE cH i q hker hq s hs

local notation "δ" => actionDefect I cE cH i q hker hq s hs

omit [DecidableEq I] [Mono i.hom.hom] in
theorem actionDefect_comp {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ (𝔻).X)
    (x : T ⟶ H.X) :
    δ t x ≫ i.hom.hom = cE.act t (x ≫ s) * (cH.act t x ≫ s)⁻¹ := by
  rw [actionDefect, Category.assoc, kernelActionDefect_comp, actionDefectUniversal,
    MonObj.comp_mul, GrpObj.comp_inv, cE.naturality, ← Category.assoc, ← Category.assoc,
    cH.naturality, lift_fst, lift_snd]

omit [DecidableEq I] [Mono i.hom.hom] in
theorem comp_actionDefect {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T)
    (t : T ⟶ (𝔻).X) (x : T ⟶ H.X) :
    b ≫ δ t x = δ (b ≫ t) (b ≫ x) := by
  rw [actionDefect, actionDefect, ← Category.assoc, comp_lift]

omit [DecidableEq I] in
include hi in
/-- The equivariance defect is a crossed homomorphism in the torus variable. -/
theorem actionDefect_mul {T : Over (Spec (CommRingCat.of k))} (t r : T ⟶ (𝔻).X)
    (x : T ⟶ H.X) :
    δ (t * r) x = cN.act t (δ r x) * δ t (cH.act r x) := by
  apply (cancel_mono i.hom.hom).1
  rw [MonObj.mul_comp, ← hi, actionDefect_comp, actionDefect_comp, actionDefect_comp,
    cE.act_mul_right, AutomorphicAction.act_inv, cE.act_mul_left t r, cH.act_mul_left t r]
  group

/-! ### Averaging the defect over the torus -/

section Averaging

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The exponent-zero Laurent coefficient of `t⁻¹ · δ(t, x)` at the universal torus point
`t`: the average of the defect over the torus. -/
def actionAverageVector (x : Lie.AffinePoints H A) : Fin d → A :=
  fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
    (cN.act (laurentPoint I A)⁻¹
      (δ (laurentPoint I A) (Lie.affineMap H (laurentConst I A) x)))).toAdd j).coeff 0

/-- The averaged defect, as an actual point of the kernel. -/
def actionAveragePoint (x : Lie.AffinePoints H A) : Lie.AffinePoints N A :=
  (vectorAffineCoordinates e A).symm
    (Multiplicative.ofAdd (actionAverageVector I cE cH cN i q hker hq s hs e x))

local notation "β" => actionAverageVector I cE cH cN i q hker hq s hs e
local notation "ρ" => actionAveragePoint I cE cH cN i q hker hq s hs e

omit [Mono i.hom.hom] in
theorem actionAveragePoint_coordinates (x : Lie.AffinePoints H A) :
    (vectorAffineCoordinates e A (ρ x)).toAdd = β x := by
  rw [actionAveragePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

omit [DecidableEq I] [Mono i.hom.hom] in
/-- Applying a coefficient map to an actual defect. -/
theorem affineMap_actionDefect {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (t : Lie.AffinePoints (𝔻) A) (x : Lie.AffinePoints H A) :
    Lie.affineMap N φ (δ t x) = δ (Lie.affineMap _ φ t) (Lie.affineMap _ φ x) :=
  comp_actionDefect I cE cH i q hker hq s hs _ t x

/-- The scheme section corrected by the averaged defect. -/
def equivariantSectionPoint (x : Lie.AffinePoints H A) : Lie.AffinePoints E A :=
  (ρ x ≫ i.hom.hom)⁻¹ * (x ≫ s)

local notation "σ" => equivariantSectionPoint I cE cH cN i q hker hq s hs e

variable [IsAffineHom H.X.hom]

/-- The corrected section as a morphism of schemes. -/
def equivariantSection : H.X ⟶ E.X :=
  homOfAffinePoints fun _ _ _ x => σ x

variable [IsAffineHom N.X.hom] (he : IsLinearVectorCoordinates cN e)
include he

omit [IsAffineHom H.X.hom] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- The average is invariant under translation of the averaging variable. -/
theorem actionAverageVector_translate (r : Lie.AffinePoints (𝔻) A)
    (x : Lie.AffinePoints H A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (cN.act (Lie.affineMap _ (laurentConst I A) r * laurentPoint I A)⁻¹
        (δ (Lie.affineMap _ (laurentConst I A) r * laurentPoint I A)
          (Lie.affineMap H (laurentConst I A) x)))).toAdd j).coeff 0) =
      β x := by
  let τ := (laurentTranslation I (algebraPointsEquiv I A r)).restrictScalars k
  rw [← laurentTranslation_laurentPoint, ← laurentTranslation_laurentConst I
    (algebraPointsEquiv I A r) x, ← affineMap_actionDefect, ← map_inv,
    ← cN.affineAct_naturality, he.1.vectorAffineCoordinates_naturality]
  funext j
  exact coeff_zero_laurentTranslation I _ _

omit [DecidableEq I] [IsAffineHom H.X.hom] [IsAffineHom N.X.hom]
  [Mono i.hom.hom] in
/-- Constant Laurent coefficients of a constant point. -/
theorem coeff_zero_laurentConst_kernel (x : Lie.AffinePoints N A) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (Lie.affineMap N (laurentConst I A) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A x).toAdd := by
  rw [he.1.vectorAffineCoordinates_naturality]
  funext j
  change (AddMonoidAlgebra.single 0 _).coeff 0 = _
  simp

omit [DecidableEq I] [IsAffineHom H.X.hom] [Mono i.hom.hom] in
/-- Constant Laurent coefficients of the action of a constant torus point. -/
theorem coeff_zero_kernelAct (r : Lie.AffinePoints (𝔻) A)
    (x : Lie.AffinePoints N (AddMonoidAlgebra A (I → ℤ))) :
    (fun j => ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ))
      (cN.act (Lie.affineMap _ (laurentConst I A) r) x)).toAdd j).coeff 0) =
      (vectorAffineCoordinates e A (cN.act r ((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (fun j =>
          ((vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ)) x).toAdd j).coeff 0))))).toAdd :=
    by
  have hx := he.coordinateAction_eq (CommAlgCat.of k (AddMonoidAlgebra A (I → ℤ)))
    (Lie.affineMap _ (laurentConst I A) r)
    (vectorAffineCoordinates e (AddMonoidAlgebra A (I → ℤ)) x).toAdd
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at hx
  rw [← hx, cN.coordinateAction_coeff, he.coordinateAction_eq]

omit [IsAffineHom H.X.hom] in
include hi in
/-- The defect is the coboundary of the average: `r · ρ(x) = δ(r, x) · ρ(r · x)`. -/
theorem act_actionAveragePoint (r : Lie.AffinePoints (𝔻) A) (x : Lie.AffinePoints H A) :
    cN.act r (ρ x) = δ r x * ρ (cH.act r x) := by
  let L := AddMonoidAlgebra A (I → ℤ)
  let t₀ := laurentPoint (k := k) I A
  let rL := Lie.affineMap (𝔻) (laurentConst I A) r
  let xL := Lie.affineMap H (laurentConst I A) x
  have hc := actionDefect_mul I cE cH cN i q hker hq hi s hs t₀ rL xL
  -- act by `t₀⁻¹` on both sides
  have hc' : cN.act rL (cN.act (rL * t₀)⁻¹ (δ (rL * t₀) xL)) =
      δ rL xL * cN.act t₀⁻¹ (δ t₀ (cH.act rL xL)) := by
    rw [← points_mul_comm I t₀ rL, ← cN.act_mul_left, hc, cN.act_mul_right,
      ← cN.act_mul_left, show rL * (t₀ * rL)⁻¹ * t₀ = 1 by group,
      cN.act_one_left, show rL * (t₀ * rL)⁻¹ = t₀⁻¹ by group]
  have hrx : cH.act rL xL = Lie.affineMap H (laurentConst I A) (cH.act r x) :=
    (cH.affineAct_naturality _ r x).symm
  have hδ : δ rL xL = Lie.affineMap N (laurentConst I A) (δ r x) :=
    (affineMap_actionDefect I cE cH i q hker hq s hs _ r x).symm
  rw [hrx, hδ] at hc'
  have hcoeff := congrArg (fun z : Lie.AffinePoints N L =>
      fun j : Fin d => ((vectorAffineCoordinates e L z).toAdd j).coeff 0) hc'
  simp only at hcoeff
  rw [coeff_zero_kernelAct I cN e he r, actionAverageVector_translate I cE cH cN i q hker hq s
    hs e he r x] at hcoeff
  simp only [map_mul, toAdd_mul, Pi.add_apply] at hcoeff
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  rw [map_mul, toAdd_mul]
  have h1 := coeff_zero_laurentConst_kernel I cN e he (δ r x)
  have h2 : (fun j => ((vectorAffineCoordinates e L
      (cN.act t₀⁻¹ (δ t₀ (Lie.affineMap H (laurentConst I A) (cH.act r x))))).toAdd j).coeff 0) =
      β (cH.act r x) := rfl
  have hβ : (vectorAffineCoordinates e A (ρ x)) = Multiplicative.ofAdd (β x) := by
    rw [actionAveragePoint, MulEquiv.apply_symm_apply]
  rw [← hβ, MulEquiv.symm_apply_apply] at hcoeff
  rw [actionAveragePoint_coordinates, hcoeff]
  funext j
  rw [Pi.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← congrFun h1 j,
    ← congrFun h2 j]

omit [IsAffineHom H.X.hom] in
include hi in
/-- The corrected section is equivariant on affine points. -/
theorem act_equivariantSectionPoint (r : Lie.AffinePoints (𝔻) A) (x : Lie.AffinePoints H A) :
    cE.act r (σ x) = σ (cH.act r x) := by
  simp only [equivariantSectionPoint]
  rw [cE.act_mul_right, AutomorphicAction.act_inv, hi,
    act_actionAveragePoint I cE cH cN i q hker hq hi s hs e he, MonObj.mul_comp,
    actionDefect_comp I cE cH i q hker hq s hs r x]
  group

omit [IsAffineHom H.X.hom] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- The average commutes with extension of coefficients. -/
theorem actionAverageVector_naturality {B : Type u} [CommRing B] [Algebra k B] (φ : A →ₐ[k] B)
    (x : Lie.AffinePoints H A) :
    β (Lie.affineMap _ φ x) = fun j => φ (β x j) := by
  have hc : (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ).comp (laurentConst I A) =
      (laurentConst I B).comp φ := by
    ext a
    simp [laurentConst, AddMonoidAlgebra.coe_algebraMap]
  have hl : (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ).comp (laurentScalars I A) =
      laurentScalars I B := by
    rw [laurentScalars, laurentScalars, ← AddMonoidAlgebra.mapRangeAlgHom_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have hp : Lie.affineMap (𝔻) (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ) (laurentPoint I A) =
      laurentPoint I B := by
    rw [laurentPoint, laurentPoint, ← Lie.affineMap_comp, hl]
  have hx : Lie.affineMap H (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ)
      (Lie.affineMap H (laurentConst I A) x) =
      Lie.affineMap H (laurentConst I B) (Lie.affineMap H φ x) := by
    rw [← Lie.affineMap_comp, ← Lie.affineMap_comp, hc]
  have hd : cN.act (laurentPoint I B)⁻¹
      (δ (laurentPoint I B) (Lie.affineMap H (laurentConst I B) (Lie.affineMap _ φ x))) =
      Lie.affineMap N (AddMonoidAlgebra.mapAlgHom (I → ℤ) φ)
        (cN.act (laurentPoint I A)⁻¹
          (δ (laurentPoint I A) (Lie.affineMap H (laurentConst I A) x))) := by
    rw [cN.affineAct_naturality, affineMap_actionDefect, map_inv, hp, hx]
  funext j
  simp only [actionAverageVector]
  rw [hd, he.1.vectorAffineCoordinates_naturality]
  exact AddMonoidAlgebra.coeff_mapAlgHom _ _ _

omit [IsAffineHom H.X.hom] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- The averaged point commutes with extension of coefficients. -/
theorem actionAveragePoint_naturality {B : Type u} [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (x : Lie.AffinePoints H A) :
    Lie.affineMap N φ (ρ x) = ρ (Lie.affineMap _ φ x) := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.1.vectorAffineCoordinates_naturality, actionAveragePoint_coordinates,
    actionAveragePoint_coordinates, actionAverageVector_naturality I cE cH cN i q hker hq s hs e he]

omit [IsAffineHom H.X.hom] [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- The corrected section commutes with extension of coefficients. -/
theorem equivariantSectionPoint_naturality {B : Type u} [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (x : Lie.AffinePoints H A) :
    Lie.affineMap E φ (σ x) = σ (Lie.affineMap _ φ x) := by
  rw [equivariantSectionPoint, equivariantSectionPoint, map_mul, map_inv,
    ← actionAveragePoint_naturality I cE cH cN i q hker hq s hs e he]
  simp only [Lie.affineMap_apply, Category.assoc]

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- The morphism of the corrected section on affine points. -/
theorem comp_equivariantSection (x : Lie.AffinePoints H A) :
    x ≫ equivariantSection I cE cH cN i q hker hq s hs e = σ x :=
  comp_homOfAffinePoints _
    (fun _ _ _ _ _ _ f v => equivariantSectionPoint_naturality I cE cH cN i q hker hq s hs e he f v)
    x

omit [IsAffineHom N.X.hom] [Mono i.hom.hom] in
/-- The corrected section is a section of the quotient map on schemes. -/
theorem equivariantSection_comp :
    equivariantSection I cE cH cN i q hker hq s hs e ≫ q.hom.hom = 𝟙 H.X := by
  have hiq : i.hom.hom ≫ q.hom.hom = 1 :=
    (hker _ _).1 (SubgroupFunctor.mem_range.2 ⟨𝟙 _, Category.id_comp _⟩)
  apply affine_hom_ext
  intro A _ _ x
  rw [← Category.assoc, comp_equivariantSection I cE cH cN i q hker hq s hs e he,
    equivariantSectionPoint, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc,
    hs, hiq, MonObj.comp_one, inv_one, one_mul, Category.comp_id]

attribute [local instance] isAffineHom_splitTorus_spec

include hi in
/-- The corrected section is equivariant on all points. -/
theorem act_equivariantSection {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ (𝔻).X)
    (x : T ⟶ H.X) :
    cE.act t (x ≫ equivariantSection I cE cH cN i q hker hq s hs e) =
      cH.act t x ≫ equivariantSection I cE cH cN i q hker hq s hs e := by
  have huniv : cE.act (fst (𝔻).X H.X)
      (snd (𝔻).X H.X ≫ equivariantSection I cE cH cN i q hker hq s hs e) =
      cH.act (fst (𝔻).X H.X) (snd (𝔻).X H.X) ≫
        equivariantSection I cE cH cN i q hker hq s hs e := by
    apply affine_hom_ext
    intro A _ _ v
    rw [cE.naturality, ← Category.assoc, ← Category.assoc, cH.naturality,
      comp_equivariantSection I cE cH cN i q hker hq s hs e he,
      comp_equivariantSection I cE cH cN i q hker hq s hs e he,
      act_equivariantSectionPoint I cE cH cN i q hker hq hi s hs e he]
  have h := congrArg (fun F => lift t x ≫ F) huniv
  rw [cE.naturality, ← Category.assoc, ← Category.assoc, cH.naturality, lift_fst,
    lift_snd] at h
  exact h

end Averaging

end splitTorus

open RelativeRoot in
/-- **Equivariant sections.** A split torus acts compatibly on a group scheme `E`, on a
quotient `q : E ⟶ H` with affine `H`, and on its kernel `N`, an affine vector group with
linear coordinates. If `q` has a section as a morphism of schemes, it has an equivariant
one. -/
theorem IsSplitTorus.exists_equivariantSection {k : Type u} [Field k]
    {D E H N : GroupScheme (Spec (CommRingCat.of k))} (hD : IsSplitTorus D)
    [IsAffineHom H.X.hom] [IsAffineHom N.X.hom]
    (cE : AutomorphicAction D E) (cH : AutomorphicAction D H) (cN : AutomorphicAction D N)
    (i : N ⟶ E) [Mono i.hom.hom] (q : E ⟶ H)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (g : T ⟶ E.X),
      cE.act t g ≫ q.hom.hom = cH.act t (g ≫ q.hom.hom))
    (hi : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (w : T ⟶ N.X),
      cE.act t (w ≫ i.hom.hom) = cN.act t w ≫ i.hom.hom)
    (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 _) {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ N.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (he : IsLinearVectorCoordinates cN e) :
    ∃ σ : H.X ⟶ E.X, σ ≫ q.hom.hom = 𝟙 _ ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ D.X) (x : T ⟶ H.X),
        cE.act t (x ≫ σ) = cH.act t x ≫ σ := by
  classical
  obtain ⟨I, hI, ⟨f⟩⟩ := hD
  have : Fintype I := Fintype.ofFinite I
  have hfi : f.hom.hom.hom ≫ f.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, f.hom_inv_id, Grp.id_hom_hom]
  have hq' : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (g : T ⟶ E.X),
      (cE.restrict f.inv).act t g ≫ q.hom.hom = (cH.restrict f.inv).act t (g ≫ q.hom.hom) := by
    intro T t g
    simp only [AutomorphicAction.restrict_act]
    exact hq T _ g
  have hi' : ∀ (T : Over (Spec (CommRingCat.of k)))
      (t : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (w : T ⟶ N.X),
      (cE.restrict f.inv).act t (w ≫ i.hom.hom) = (cN.restrict f.inv).act t w ≫ i.hom.hom := by
    intro T t w
    simp only [AutomorphicAction.restrict_act]
    exact hi T _ w
  have he' : IsLinearVectorCoordinates (cN.restrict f.inv) e := by
    refine ⟨he.1, fun T h c v => ?_⟩
    simp only [AutomorphicAction.restrict_act]
    exact he.2 T _ c v
  refine ⟨splitTorus.equivariantSection I (cE.restrict f.inv) (cH.restrict f.inv)
      (cN.restrict f.inv) i q hker hq' s hs e,
    splitTorus.equivariantSection_comp I (cE.restrict f.inv) (cH.restrict f.inv)
      (cN.restrict f.inv) i q hker hq' s hs e he', ?_⟩
  intro T t x
  have h := splitTorus.act_equivariantSection I (cE.restrict f.inv) (cH.restrict f.inv)
    (cN.restrict f.inv) i q hker hq' hi' s hs e he' (t ≫ f.hom.hom.hom) x
  simp only [AutomorphicAction.restrict_act, Category.assoc, hfi, Category.comp_id] at h
  exact h

end Langlands.GroupScheme
