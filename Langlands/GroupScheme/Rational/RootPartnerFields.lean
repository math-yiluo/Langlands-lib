import Langlands.Algebra.QuadraticFixedFields
import Langlands.GroupScheme.Reductive.RootDatumOrbitPartners
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Rational.RootGaloisOrbits
import Langlands.GroupScheme.Torus.SplitPartCharacterTrace

/-! # Fields of an absolute root and of its sum with an orbit partner -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry IntermediateField

namespace Langlands.GroupScheme

namespace RootPartnerFields

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- An orbit partner of an actual root `β`: a different member `β'` of the Galois orbit of
`β` such that `β + β'` is an actual root. -/
def IsRootPartner (β β' : roots (T := T_L) (G := G_L) j_L) : Prop :=
  (∃ σ : L ≃ₐ[k] L, σ • β = β') ∧ β' ≠ β ∧
    β.val + β'.val ∈ roots (T := T_L) (G := G_L) j_L

/-- The field of an actual root has the stabilizer of the root as fixing subgroup. -/
theorem fixingSubgroup_rootOrbitField [FiniteDimensional k L]
    (β : roots (T := T_L) (G := G_L) j_L) :
    (rootOrbitField k L j β).fixingSubgroup = MulAction.stabilizer (L ≃ₐ[k] L) β :=
  IntermediateField.fixingSubgroup_fixedField _

section RootDatum

variable [LocallyOfFiniteType G.X.hom]
  {j} (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
  (hj : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k L)).map j).hom.hom.left)
  {J : Type*}
  {P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j) P)

omit [LocallyOfFiniteType G.X.hom] in
include hP in
theorem root_mem_roots (m : J) : P.root m ∈ roots (T := T_L) (G := G_L) j_L := by
  rw [← hP.2.1]
  exact ⟨m, rfl⟩

omit [LocallyOfFiniteType G.X.hom] in
include hP in
theorem exists_root_eq (β : roots (T := T_L) (G := G_L) j_L) : ∃ p : J, P.root p = β.val := by
  have h : β.val ∈ Set.range P.root := by
    rw [hP.2.1]
    exact β.property
  exact h

/-- The Galois root-datum action on root indices lifts the Galois action on roots. -/
theorem root_smul (σ : L ≃ₐ[k] L) (p : J) :
    P.root (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP σ • p) =
      characterLattice.galoisRepresentation k L T σ (P.root p) :=
  IsRootDatumOf.galoisRootIndexEquiv_root k L j hP σ p

variable [Fintype (L ≃ₐ[k] L)]

/-- The orbit sums of the root datum are the Galois orbit sums of characters. -/
theorem orbitSum_eq_galoisOrbitSum (p : J) :
    RootPairing.OrbitPartner.orbitSum P
        (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP) p =
      CharacterAveraging.galoisOrbitSum k L T (P.root p) := by
  unfold RootPairing.OrbitPartner.orbitSum CharacterAveraging.galoisOrbitSum
    CocharacterAveraging.orbitSum
  exact Finset.sum_congr rfl fun σ _ => root_smul k L hT hj hP σ p

/-- Nonvanishing Galois orbit sums of actual roots give the standing hypothesis of
`RootPairing.OrbitPartner`. -/
theorem orbitSum_ne_zero
    (hne : ∀ γ : roots (T := T_L) (G := G_L) j_L,
      CharacterAveraging.galoisOrbitSum k L T γ.val ≠ 0) (m : J) :
    RootPairing.OrbitPartner.orbitSum P
      (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP) m ≠ 0 := by
  rw [orbitSum_eq_galoisOrbitSum k L hT hj hP]
  exact hne ⟨P.root m, root_mem_roots k L hP m⟩

omit [Fintype (L ≃ₐ[k] L)] in
/-- Root-index stabilizers are the stabilizers of the actual roots. -/
theorem stabilizer_eq {p : J} {β : roots (T := T_L) (G := G_L) j_L} (hp : P.root p = β.val) :
    RootPairing.OrbitPartner.stabilizer P
        (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP) p =
      MulAction.stabilizer (L ≃ₐ[k] L) β := by
  ext σ
  rw [RootPairing.OrbitPartner.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    apply Subtype.ext
    rw [rootsGaloisAction_coe, ← hp, ← root_smul k L hT hj hP, h]
  · intro h
    apply P.root.injective
    rw [root_smul k L hT hj hP, hp, ← rootsGaloisAction_coe, h]

omit [Fintype (L ≃ₐ[k] L)] in
/-- Actual root partners are orbit partners of root indices. -/
theorem isOrbitPartner {β β' : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') {p q : J} (hp : P.root p = β.val) (hq : P.root q = β'.val) :
    RootPairing.OrbitPartner.IsOrbitPartner P
      (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP) p q := by
  obtain ⟨⟨σ, hσ⟩, hne, hsum⟩ := h
  refine ⟨⟨σ, ?_⟩, ?_, ?_⟩
  · apply P.root.injective
    rw [root_smul k L hT hj hP, hp, hq, ← rootsGaloisAction_coe, hσ]
  · intro hqp
    apply hne
    apply Subtype.ext
    rw [← hp, ← hq, hqp]
  · rw [hp, hq, hP.2.1]
    exact hsum

variable [Finite J]
  (hne : ∀ γ : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j),
    CharacterAveraging.galoisOrbitSum k L T γ.val ≠ 0)

include hT hj hP hne

/-- A Galois element moving a root to its partner moves the partner back. -/
theorem smul_partner {β β' : roots (T := T_L) (G := G_L) j_L} (h : IsRootPartner k L j β β')
    {σ : L ≃ₐ[k] L} (hσ : σ • β = β') : σ • β' = β := by
  obtain ⟨p, hp⟩ := exists_root_eq k L hP β
  obtain ⟨q, hq⟩ := exists_root_eq k L hP β'
  have hpq := isOrbitPartner k L hT hj hP h hp hq
  have hne' := orbitSum_ne_zero k L hT hj hP hne
  have hσp : IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP σ • p = q := by
    apply P.root.injective
    rw [root_smul k L hT hj hP, hp, hq, ← rootsGaloisAction_coe, hσ]
  have h' := hpq.smul σ
  rw [hσp] at h'
  have hσq := hpq.symm.unique hne' h'
  apply Subtype.ext
  rw [rootsGaloisAction_coe, ← hq, ← root_smul k L hT hj hP, hσq, hp]

/-- The stabilizer of a root lies in the stabilizer of its sum with its partner, with
relative index two. -/
theorem stabilizer_le_and_relIndex {β β' μ : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val) :
    MulAction.stabilizer (L ≃ₐ[k] L) β ≤ MulAction.stabilizer (L ≃ₐ[k] L) μ ∧
      (MulAction.stabilizer (L ≃ₐ[k] L) β).relIndex (MulAction.stabilizer (L ≃ₐ[k] L) μ) =
        2 := by
  obtain ⟨p, hp⟩ := exists_root_eq k L hP β
  obtain ⟨q, hq⟩ := exists_root_eq k L hP β'
  obtain ⟨m, hm⟩ := exists_root_eq k L hP μ
  have hpq := isOrbitPartner k L hT hj hP h hp hq
  have hne' := orbitSum_ne_zero k L hT hj hP hne
  have hroot : P.root m = P.root p + P.root q := by rw [hm, hp, hq, hμ]
  rw [← stabilizer_eq k L hT hj hP hp, ← stabilizer_eq k L hT hj hP hm]
  exact ⟨hpq.stabilizer_le hne' hroot, hpq.relIndex_stabilizer hne' hroot⟩

/-- The field of the sum of a root with its partner lies in the field of the root. -/
theorem rootOrbitField_le {β β' μ : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val) :
    rootOrbitField k L j μ ≤ rootOrbitField k L j β :=
  IntermediateField.fixedField_le (stabilizer_le_and_relIndex k L hT hj hP hne h hμ).1

variable [FiniteDimensional k L]

/-- The fixing subgroups of these two fields have relative index two. -/
theorem relIndex_fixingSubgroup {β β' μ : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val) :
    (rootOrbitField k L j β).fixingSubgroup.relIndex
      (rootOrbitField k L j μ).fixingSubgroup = 2 := by
  rw [fixingSubgroup_rootOrbitField, fixingSubgroup_rootOrbitField]
  exact (stabilizer_le_and_relIndex k L hT hj hP hne h hμ).2

variable [IsGalois k L]
  {β β' μ : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j)}
  [Algebra (rootOrbitField k L j μ) (rootOrbitField k L j β)]
  [IsScalarTower (rootOrbitField k L j μ) (rootOrbitField k L j β) L]

/-- **The field of a root is quadratic over the field of its sum with its partner.** -/
theorem isQuadraticExtension (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val) :
    Algebra.IsQuadraticExtension (rootOrbitField k L j μ) (rootOrbitField k L j β) :=
  Langlands.Algebra.QuadraticFixedFields.isQuadraticExtension _ _
    (relIndex_fixingSubgroup k L hT hj hP hne h hμ)

omit [LocallyOfFiniteType G.X.hom] [Fintype (L ≃ₐ[k] L)] [FiniteDimensional k L]
  hT hj hP hne in
/-- The field of a root is separable over the field of its sum with its partner. -/
theorem isSeparable : Algebra.IsSeparable (rootOrbitField k L j μ) (rootOrbitField k L j β) :=
  Langlands.Algebra.QuadraticFixedFields.isSeparable _ _

/-- **Conjugation of the field of a multipliable root.** A Galois element moving a root to
its partner acts on the field of the root as the conjugation over the field of the sum. -/
theorem conjugation_apply (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val)
    {σ : L ≃ₐ[k] L} (hσ : σ • β = β') (x : rootOrbitField k L j β) :
    haveI := isQuadraticExtension k L hT hj hP hne h hμ
    haveI := isSeparable k L (j := j) (β := β) (μ := μ)
    (SU3Root.conjugation (rootOrbitField k L j μ) (rootOrbitField k L j β) x : L) = σ x := by
  have := isQuadraticExtension k L hT hj hP hne h hμ
  have := isSeparable k L (j := j) (β := β) (μ := μ)
  have hσμ : σ ∈ (rootOrbitField k L j μ).fixingSubgroup := by
    rw [fixingSubgroup_rootOrbitField, MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [rootsGaloisAction_coe, hμ, map_add, ← rootsGaloisAction_coe, ← rootsGaloisAction_coe,
      hσ, smul_partner k L hT hj hP hne h hσ, add_comm]
  have hσβ : σ ∉ (rootOrbitField k L j β).fixingSubgroup := by
    rw [fixingSubgroup_rootOrbitField, MulAction.mem_stabilizer_iff, hσ]
    exact h.2.1
  exact Langlands.Algebra.QuadraticFixedFields.conjugation_apply _ _ hσμ hσβ x

end RootDatum

end RootPartnerFields

end Langlands.GroupScheme
