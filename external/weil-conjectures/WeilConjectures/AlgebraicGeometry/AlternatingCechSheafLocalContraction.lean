/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafInsertionHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Local contraction of the increasing-tuple sheaf augmentation

Source: Stacks Project, Tag 01FM, alternating faces; local contraction paragraph of
lem-pc-s3-affine-alternating-cech-augmented-construction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-contraction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

-- Restriction detects invertibility on an open cover, including the empty cover.
private theorem isIso_of_cover_restrict {X : Scheme.{u}} {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f)) : IsIso f := by
  have : Mono f := Scheme.Modules.mono_of_restrict f U hU fun i ↦ by
    have := h i
    infer_instance
  have : Epi f := (Preadditive.epi_iff_isZero_cokernel f).2 (by
    apply Scheme.Modules.isZero_of_iSup_eq_top _ U hU
    intro i
    have := h i
    exact (CategoryTheory.Limits.PreservesCokernel.iso
      (Scheme.Modules.restrictFunctor (U i).ι) f).isZero_iff.mpr
      (CategoryTheory.Limits.isZero_cokernel_of_epi _))
  exact isIso_of_mono_of_epi f

-- Exact restriction commutes with homology, for any complex shape.
private theorem quasiIso_of_cover_restrict {X : Scheme.{u}} {ι : Type*}
    {J : Type} (c : ComplexShape J) (U : ι → X.Opens) (hU : iSup U = ⊤)
    {K L : HomologicalComplex X.Modules c} (f : K ⟶ L)
    (h : ∀ i, QuasiIso (((Scheme.Modules.restrictFunctor (U i).ι).mapHomologicalComplex
      c).map f)) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  apply isIso_of_cover_restrict U hU
  intro i
  let R := Scheme.Modules.restrictFunctor (U i).ι
  let φ := (HomologicalComplex.shortComplexFunctor X.Modules c n).map f
  have hφ : ShortComplex.QuasiIso (R.mapShortComplex.map φ) := by
    have := h i
    exact (quasiIsoAt_iff ((R.mapHomologicalComplex c).map f) n).mp inferInstance
  have : IsIso (ShortComplex.homologyMap (R.mapShortComplex.map φ)) :=
    (ShortComplex.quasiIso_iff _).mp hφ
  have he := ShortComplex.mapHomologyIso_inv_naturality φ R
  have : IsIso (R.map (ShortComplex.homologyMap φ) ≫
      ((L.sc n).mapHomologyIso R).inv) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ ((L.sc n).mapHomologyIso R).inv).mp inferInstance

-- Identify the explicit tensor formula with the canonical pullback by adjunction.
private noncomputable def tensorPullbackIsoPullback {X Y : Scheme.{u}} (p : Y ⟶ X) :
    Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
  (Scheme.Modules.nonempty_tensorPullbackAdjunction p).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction p)

-- Pullback followed by open restriction factors through restriction on the source.
private noncomputable def tensorPullbackRestrictIso {X Y : Scheme.{u}}
    (p : Y ⟶ X) (W : X.Opens) :
    Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.restrictFunctor (p ⁻¹ᵁ W).ι ≅
      Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.pullback (p ∣_ W) :=
  Functor.isoWhiskerRight (tensorPullbackIsoPullback p) _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback _) ≪≫
    Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι p W).symm ≪≫
    (Scheme.Modules.pullbackComp _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback W.ι).symm _

private theorem local_homotopyEquivalence_tensorPullback {X Y : Scheme.{u}}
    (p : Y ⟶ X) [(Scheme.Modules.tensorPullback p).Additive]
    (W : X.Opens) {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (h : HomologicalComplex.homotopyEquivalences W.toScheme.Modules (ComplexShape.up ℤ)
      (((Scheme.Modules.restrictFunctor W.ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)) :
    HomologicalComplex.homotopyEquivalences (p ⁻¹ᵁ W).toScheme.Modules (ComplexShape.up ℤ)
      (((Scheme.Modules.restrictFunctor (p ⁻¹ᵁ W).ι).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((Scheme.Modules.tensorPullback p).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)) := by
  obtain ⟨e, he⟩ := h
  let F := Scheme.Modules.pullback (p ∣_ W)
  have hm := (F.mapHomotopyEquiv e).homotopyEquivalences_hom
  rw [Functor.mapHomotopyEquiv_hom, he] at hm
  let α := NatIso.mapHomologicalComplex (tensorPullbackRestrictIso p W) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.homotopyEquivalences _ _).arrow_mk_iso_iff
    (Arrow.isoMk (α.app K) (α.app L) (α.hom.naturality f).symm)).mpr hm

/-- The explicit sheaf augmentation is a quasi-isomorphism, also after tensor pullback.
Source: Stacks Project, Tag 01FM, signed ordered faces, and the local contraction
paragraph of lem-pc-s3-affine-alternating-cech-augmented-construction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-contraction).

Proof: Restrict the augmented complex to U_i. Its term at a tuple t has sections of
G on V intersect U_i intersect the opens of t. Insert i into t in its unique ordered
position, with sign (-1) to that position, and set the operator to zero if i occurs
already. This is linear over O(V) and commutes with restrictions of V. In degree zero
the contracting map to G is the projection to the singleton i. In the differential
homotopy identity the face deleting the inserted i has coefficient one and returns
the original tuple. For each other face, deleting that face before inserting i and
after inserting i produces the same restriction composite with opposite coefficients.
If i occurs already, only its deletion contributes to the identity. Thus the augmented
complex is split contractible on U_i, including its degree-zero augmentation. Restrict
along p to p inverse U_i; tensor pullback commutes with restriction to these opens.
Apply the additive tensor pullback to the local homotopy identities. It preserves
finite sums, integer multiples, composition and identities, so the pulled-back
augmentation is again a local homotopy equivalence, without assuming flatness.
The U_i and their inverse images cover. Homology of module sheaf complexes is local,
so both augmentations are quasi-isomorphisms. Extension by zero from natural to integer
degrees preserves the homotopy identities and adds only zero terms. If r=0 the cover
condition makes X empty; Y is empty as it maps to X, and all these module sheaves are zero. -/
theorem alternatingCechSheafAugmentation_quasiIso
    {X Y : Scheme.{u}} (p : Y ⟶ X)
    [(Scheme.Modules.tensorPullback p).Additive]
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤) (G : X.Modules) :
    QuasiIso (alternatingCechSheafAugmentation U G) ∧
      QuasiIso (((Scheme.Modules.tensorPullback p).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap
          (alternatingCechSheafAugmentation U G) ComplexShape.embeddingUpNat)) := by
  let ε := HomologicalComplex.extendMap
    (alternatingCechSheafAugmentation U G) ComplexShape.embeddingUpNat
  have hlocal := alternatingCechSheafAugmentation_restrict_homotopyEquivalence U G
  have hε : QuasiIso ε := quasiIso_of_cover_restrict (ComplexShape.up ℤ) U hU ε
    fun i ↦ (HomologicalComplex.mem_quasiIso_iff _).mp
      (homotopyEquivalences_le_quasiIso _ _ _ (hlocal i))
  refine ⟨(HomologicalComplex.quasiIso_extendMap_iff _ _).mp hε, ?_⟩
  apply quasiIso_of_cover_restrict (ComplexShape.up ℤ) (fun i ↦ p ⁻¹ᵁ U i)
    (p.iSup_preimage_eq_top hU)
  intro i
  exact (HomologicalComplex.mem_quasiIso_iff _).mp
    (homotopyEquivalences_le_quasiIso _ _ _
      (local_homotopyEquivalence_tensorPullback p (U i) ε (hlocal i)))

end AlgebraicGeometry
