import Langlands.GroupScheme.FiniteEtaleImage
import Langlands.GroupScheme.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.Topology.Connected.Clopen

/-! # Clopen subgroups of normal subgroups in connected families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClopenNormalSubgroup

variable {S : Scheme.{u}} {G K P : GroupScheme S}
  (i : K ⟶ G) (j : P ⟶ K)
  (hn : (SubgroupFunctor.range i).IsNormal)

/-- Ambient conjugation of a point in the supplied subgroup. -/
def conjOver : G.X ⊗ P.X ⟶ G.X :=
  (G.X ◁ (j ≫ i).hom.hom) ≫ GrpObj.conj G.X

theorem lift_conjOver {T : Over S} (g : T ⟶ G.X) (y : T ⟶ P.X) :
    lift g y ≫ conjOver i j = g * (y ≫ (j ≫ i).hom.hom) * g⁻¹ := by
  rw [conjOver, lift_whiskerLeft_assoc, GrpObj.lift_conj_eq_mul_mul_inv]

include hn in
/-- Normality gives an actual factorization of conjugation through `K`. -/
theorem exists_conjToNormal :
    ∃ c : G.X ⊗ P.X ⟶ K.X, c ≫ i.hom.hom = conjOver i j := by
  have h := hn (G.X ⊗ P.X) (fst G.X P.X)
    (snd G.X P.X ≫ (j ≫ i).hom.hom) (Subgroup.mem_top _)
    (SubgroupFunctor.mem_range.mpr ⟨snd G.X P.X ≫ j.hom.hom, rfl⟩)
  have he : conjOver i j = fst G.X P.X *
      (snd G.X P.X ≫ (j ≫ i).hom.hom) * (fst G.X P.X)⁻¹ := by
    simpa only [lift_fst_snd, Category.id_comp] using
      lift_conjOver i j (fst G.X P.X) (snd G.X P.X)
  rw [← he] at h
  exact SubgroupFunctor.mem_range.mp h

/-- Conjugation with codomain restricted to the normal subgroup. -/
def conjToNormal : G.X ⊗ P.X ⟶ K.X := (exists_conjToNormal i j hn).choose

@[reassoc (attr := simp)]
theorem conjToNormal_fac : conjToNormal i j hn ≫ i.hom.hom = conjOver i j :=
  (exists_conjToNormal i j hn).choose_spec

/-- The section of the second projection given by the identity in `G`. -/
def identitySection : P.X ⟶ G.X ⊗ P.X :=
  lift (toUnit P.X ≫ η[G.X]) (𝟙 P.X)

@[reassoc (attr := simp)]
theorem identitySection_snd : identitySection (G := G) (P := P) ≫ snd G.X P.X = 𝟙 P.X :=
  lift_snd _ _

@[reassoc (attr := simp)]
theorem identitySection_conjOver : identitySection (G := G) (P := P) ≫ conjOver i j =
    (j ≫ i).hom.hom := by
  rw [identitySection, lift_conjOver, ← CategoryTheory.Hom.one_def]
  simp

variable [Mono i.hom.hom]

@[reassoc (attr := simp)]
theorem identitySection_conjToNormal :
    identitySection (G := G) (P := P) ≫ conjToNormal i j hn = j.hom.hom := by
  apply (cancel_mono i.hom.hom).mp
  rw [Category.assoc, conjToNormal_fac, identitySection_conjOver]
  rfl

variable [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]
  [GeometricallyConnected G.X.hom]

/-- Conjugation lands in the clopen subgroup: each connected projection fibre
meets its clopen inverse image along the identity section. -/
theorem range_conjToNormal_subset :
    Set.range (conjToNormal i j hn).left ⊆ Set.range j.hom.hom.left := by
  rintro _ ⟨z, rfl⟩
  let p : (G.X ⊗ P.X).left ⟶ P.X.left := pullback.snd G.X.hom P.X.hom
  let s : P.X ⟶ G.X ⊗ P.X := identitySection
  have hF : _root_.IsConnected (p ⁻¹' {p z}) :=
    Scheme.Hom.isConnected_preimage_singleton p (p z)
  have hW : IsClopen ((conjToNormal i j hn).left ⁻¹' Set.range j.hom.hom.left) :=
    ⟨j.hom.hom.left.isClosedEmbedding.isClosed_range.preimage
        (conjToNormal i j hn).left.continuous,
      (IsOpenImmersion.isOpen_range j.hom.hom.left).preimage
        (conjToNormal i j hn).left.continuous⟩
  have hsF : s.left (p z) ∈ p ⁻¹' {p z} := by
    change (s ≫ snd G.X P.X).left (p z) = p z
    rw [identitySection_snd]
    rfl
  have hsW : s.left (p z) ∈
      (conjToNormal i j hn).left ⁻¹' Set.range j.hom.hom.left := by
    change (conjToNormal i j hn).left (s.left (p z)) ∈ Set.range j.hom.hom.left
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, identitySection_conjToNormal]
    exact ⟨p z, rfl⟩
  exact hF.isPreconnected.subset_isClopen hW ⟨s.left (p z), hsF, hsW⟩ rfl

/-- The actual restricted conjugation morphism `G ×_S P → P`. -/
def conjugation : G.X ⊗ P.X ⟶ P.X :=
  FiniteEtaleImage.liftOver j.hom.hom (conjToNormal i j hn)
    (range_conjToNormal_subset i j hn)

@[reassoc (attr := simp)]
theorem conjugation_fac_j : conjugation i j hn ≫ j.hom.hom = conjToNormal i j hn :=
  FiniteEtaleImage.liftOver_fac _ _ _

@[reassoc (attr := simp)]
theorem conjugation_fac : conjugation i j hn ≫ (j ≫ i).hom.hom = conjOver i j := by
  rw [Grp.comp_hom_hom, ← Category.assoc, conjugation_fac_j, conjToNormal_fac]

include hn in
/-- The clopen subgroup is normal on every scheme test. -/
theorem isNormal_range_comp : (SubgroupFunctor.range (j ≫ i)).IsNormal := by
  intro T g x _ hx
  rw [SubgroupFunctor.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨lift g y ≫ conjugation i j hn, ?_⟩
  rw [Category.assoc, conjugation_fac, lift_conjOver]

end Langlands.GroupScheme.ClopenNormalSubgroup
