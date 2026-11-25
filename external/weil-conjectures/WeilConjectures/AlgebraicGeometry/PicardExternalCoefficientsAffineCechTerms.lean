/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ExternalTensorAffineOpenSections
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Normalized affine-right Cech term comparisons

Source: Stacks Project, Tag 0BED, lemma-kunneth, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms).
-/

@[expose] public section

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X Y : Scheme.{w}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
variable (F : X.Modules) (G : Y.Modules) {ι : Type w} (U : ι → X.Opens) (V : Y.Opens)

/-- The additive-group complex on the inverse image of V.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechLeft : CochainComplex AddCommGrpCat.{w} ℕ :=
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := (externalCupCoefficients f g F G).restrict W.ι
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  ((forget₂ (ModuleCat.{w} Γ(W.toScheme, ⊤)) AddCommGrpCat.{w}).mapHomologicalComplex
    (.up ℕ)).obj ((cechComplexFunctor U').obj E.presheafModuleCat)

/-- The field-linear Cech complex with scalars restricted along f.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechBase : CochainComplex (ModuleCat.{w} k) ℕ :=
  ((ModuleCat.restrictScalars (scalarMap f ⊤)).mapHomologicalComplex (.up ℕ)).obj
    ((cechComplexFunctor U).obj F.presheafModuleCat)

/-- The fixed right tensor factor.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechFactor : ModuleCat.{w} k :=
  scalarObj (V.ι ≫ g) (G.restrict V.ι) (op ⊤)

/-- The additive-group complex obtained by termwise tensoring with G(V).
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
abbrev picardAffineCechRight : CochainComplex AddCommGrpCat.{w} ℕ :=
  ((forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).obj
    (((tensorRight (picardAffineCechFactor g G V)).mapHomologicalComplex (.up ℕ)).obj
      (picardAffineCechBase f F U))

/-- The pure external section on one intersection, constructed from the two
pullback units and the tensor section operation. No affine hypothesis is needed.
Source: Stacks Project, Tag 0BED, maps preceding equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
def picardAffineCechPureSection (n : ℕ) (y : Fin (n + 1) → ι)
    (a : (picardAffineCechBase f F U).X n) (t : picardAffineCechFactor g G V) :
    let W := (pullback.snd f g) ⁻¹ᵁ V
    let E := (externalCupCoefficients f g F G).restrict W.ι
    let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
    Γ(E, ⨅ l, U' (y l)) := by
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := externalCupCoefficients f g F G
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  let J : W.toScheme.Opens := ⨅ l, U' (y l)
  let A : X.Opens := ⨅ l, U (y l)
  let K : (Limits.pullback f g).Opens := W.ι ''ᵁ J
  have hK : K ≤ (pullback.fst f g) ⁻¹ᵁ A := by
    apply (W.ι.image_mono ?_).trans (W.ι.image_preimage_le _)
    change (⨅ l, U' (y l)) ≤ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ (⨅ l, U (y l)))
    apply le_of_eq
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage,
      Set.preimage_iInter]
    rfl
  have hKV : K ≤ (pullback.snd f g) ⁻¹ᵁ V := by
    exact (W.ι.image_mono le_top).trans_eq W.ι_image_top
  let s : Γ(F, A) := TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U F.presheafModuleCat n a y
  let t' : Γ(G, V) := G.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((G.restrictAppIso V.ι ⊤).hom t)
  let ηF := (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).unit.app F
  let ηG := (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G
  let s' : Γ((tensorPullback (pullback.fst f g)).obj F, K) :=
    ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE hK).op
      (ηF.val.app (op A) s)
  let t'' : Γ((tensorPullback (pullback.snd f g)).obj G, K) :=
    ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE hKV).op
      (ηG.val.app (op V) t')
  exact (E.restrictAppIso W.ι J).inv (tmulSection s' t'')

/-- Normalization of degreewise maps on pure tensors, coordinate by coordinate.
Source: Stacks Project, Tag 0BED, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms). -/
def PicardAffineCechNormalized
    (e : ∀ n, (picardAffineCechRight f g F G U V).X n ≅
      (picardAffineCechLeft f g F G U V).X n) : Prop :=
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := (externalCupCoefficients f g F G).restrict W.ι
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  ∀ (n : ℕ) (a : (picardAffineCechBase f F U).X n)
    (t : picardAffineCechFactor g G V) (y : Fin (n + 1) → ι),
      TopCat.Presheaf.cechComplexFunctorXAddEquiv U' E.presheafModuleCat n
        ((e n).hom (a ⊗ₜ[k] t)) y = picardAffineCechPureSection f g F G U V n y a t

/-- The native Cech coordinate equivalence respects restriction of scalars. -/
private def cechScalarCoordinates {R : Type w} [Ring R] (r : k →+* R)
    {T : TopCat.{w}} {I : Type w} (B : I → TopologicalSpace.Opens T)
    (P : (TopologicalSpace.Opens T)ᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ) :
    (ModuleCat.restrictScalars r).obj (((cechComplexFunctor B).obj P).X n) ≃ₗ[k]
      ∀ y : Fin (n + 1) → I,
        (ModuleCat.restrictScalars r).obj (P.obj (op (⨅ l, B (y l)))) where
  __ := TopCat.Presheaf.cechComplexFunctorXAddEquiv B P n
  map_smul' c a := by
    funext y
    change P.map _ (TopCat.Presheaf.cechComplexFunctorπ B P n y ((r c) • a)) =
      (r c) • P.map _ (TopCat.Presheaf.cechComplexFunctorπ B P n y a)
    change (P.map _).hom
      ((TopCat.Presheaf.cechComplexFunctorπ B P n y).hom ((r c) • a)) = _
    rw [(TopCat.Presheaf.cechComplexFunctorπ B P n y).hom.map_smul,
      (P.map _).hom.map_smul]

/-- The affine-right external section comparison is a normalized isomorphism
in each degree. This assertion has no differential or cohomology condition.
Source: Stacks Project, Tag 0BED, lemma-kunneth, affine-open paragraph;
Tags 01I9 and 01CD for affine pullback and tensor sections.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-terms).

Proof: Commute the two inverse-image maps with the finite intersections.
For each tuple, apply externalTensor_affine_open_sections to the affine
intersection of U and V. This supplies an additive equivalence from the tensor
of the two section modules to the corresponding restricted external section
module, normalized by the original projection units and tmulSection.
The native Cech coordinate equivalence is linear over the global structure ring,
since each coordinate is a module projection followed by a linear restriction.
It therefore remains k-linear after restriction of scalars. Tensor this linear
equivalence with the identity of the right factor and apply TensorProduct.piLeft
for the finite tuple set. Compose the coordinatewise chart additive equivalences
with the inverse native Cech coordinate equivalence on the left complex.
The pure-tensor formulas give the stated normalization coordinate by coordinate.
Empty tuple sets, empty intersections, empty V and zero coefficients obey these
same formulas. No covering or differential condition is used. -/
theorem picardAffineCech_normalized_terms [F.IsQuasicoherent] [G.IsQuasicoherent]
    [Finite ι]
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hV : IsAffineOpen V) :
    ∃ e : ∀ n, (picardAffineCechRight f g F G U V).X n ≅
      (picardAffineCechLeft f g F G U V).X n,
      PicardAffineCechNormalized f g F G U V e := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let W := (pullback.snd f g) ⁻¹ᵁ V
  let E := (externalCupCoefficients f g F G).restrict W.ι
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  have hJ (n : ℕ) (y : Fin (n + 1) → ι) :
      (⨅ l, U' (y l)) = W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ (⨅ l, U (y l))) := by
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage,
      Set.preimage_iInter]
    rfl
  have hK (n : ℕ) (y : Fin (n + 1) → ι) :
      W.ι ''ᵁ (⨅ l, U' (y l)) ≤ (pullback.fst f g) ⁻¹ᵁ (⨅ l, U (y l)) := by
    rw [hJ]
    exact W.ι.image_preimage_le _
  have hKV (n : ℕ) (y : Fin (n + 1) → ι) :
      W.ι ''ᵁ (⨅ l, U' (y l)) ≤ (pullback.snd f g) ⁻¹ᵁ V :=
    (W.ι.image_mono le_top).trans_eq W.ι_image_top
  choose c hc using fun n (y : Fin (n + 1) → ι) ↦
    externalTensor_affine_open_sections f g F G (⨅ l, U (y l)) V
      (hU n y) hV (⨅ l, U' (y l)) (hJ n y) (hK n y) (hKV n y)
  let M (n : ℕ) (y : Fin (n + 1) → ι) : ModuleCat.{w} k :=
    (ModuleCat.restrictScalars (scalarMap f ⊤)).obj
      (F.presheafModuleCat.obj (op (⨅ l, U (y l))))
  let N := picardAffineCechFactor g G V
  let b (n : ℕ) := cechScalarCoordinates (scalarMap f ⊤) U F.presheafModuleCat n
  let d (n : ℕ) := TopCat.Presheaf.cechComplexFunctorXAddEquiv U' E.presheafModuleCat n
  let q (n : ℕ) : ((picardAffineCechRight f g F G U V).X n) ≃+
      ((picardAffineCechLeft f g F G U V).X n) :=
    (TensorProduct.congr (b n) (LinearEquiv.refl k N)).toAddEquiv.trans
      ((TensorProduct.piLeft k N (fun y ↦ M n y)).toAddEquiv.trans
        ((AddEquiv.piCongrRight (c n)).trans (d n).symm))
  refine ⟨fun n ↦ (q n).toAddCommGrpIso, ?_⟩
  intro n a t y
  change d n (q n (a ⊗ₜ[k] t)) y = _
  change d n ((d n).symm
    ((AddEquiv.piCongrRight (c n))
      (TensorProduct.piLeft k N (fun y ↦ M n y)
        (TensorProduct.congr (b n) (LinearEquiv.refl k N) (a ⊗ₜ[k] t))))) y = _
  rw [AddEquiv.apply_symm_apply, TensorProduct.congr_tmul]
  change c n y ((TensorProduct.piLeft k N (fun y ↦ M n y))
    ((b n a) ⊗ₜ[k] t) y) = _
  have hp : (TensorProduct.piLeft k N (fun y ↦ M n y))
      ((b n a) ⊗ₜ[k] t) y = (b n a y) ⊗ₜ[k] t := by
    simp [TensorProduct.piLeft]
  rw [hp, hc]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
