import Langlands.GroupScheme.Reductive.IsogenyConjugatorUniqueness
import Langlands.GroupScheme.Reductive.IsogenyAdjointTorusDescent
import Langlands.GroupScheme.Reductive.IsogenyTorusRigidityStatement
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Torus.CharacterIsomorphism

/-! # Field specialization of relative isogeny rigidity -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- Connected reductivity is preserved by an actual supplied morphism between
field spectra, using that morphism's own coefficient map. -/
theorem IsConnectedReductive.baseChange_fieldPoint
    {k K : Type u} [Field k] [Field K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    IsConnectedReductive ((baseChange b).obj G) := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective b
  let : Algebra k K := a.hom.toAlgebra
  exact connectedReductiveFieldExtensionStatement k K G hG

/-- A connected reductive field group is reductive as a group scheme over its
field spectrum, with the original geometric fibres. -/
theorem IsConnectedReductive.isReductive
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) : IsReductive G where
  smooth := hG.smooth
  isAffineHom := hG.isAffineHom
  geometricFiber s := (hG.baseChange_fieldPoint (geometricPoint _ s)).isPseudoReductive

/-- A maximal field torus is maximal on every residue-field fibre of its field
base, including the exact coefficient maps of those fibres. -/
theorem IsMaximalTorus.isFibrewiseMaximalTorus
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) : IsFibrewiseMaximalTorus i := by
  intro s
  obtain ⟨a, ha⟩ := Spec.map_surjective ((Spec (CommRingCat.of k)).fromSpecResidueField s)
  let : Algebra k ((Spec (CommRingCat.of k)).residueField s) := a.hom.toAlgebra
  have h := (maximalTorusBaseChange k ((Spec (CommRingCat.of k)).residueField s)
    G T i hi.1 hi.2.1).mp hi
  change IsMaximalTorus
    (T := (CommGroupScheme.baseChange ((Spec (CommRingCat.of k)).fromSpecResidueField s)).obj T)
    ((baseChange ((Spec (CommRingCat.of k)).fromSpecResidueField s)).map i)
  change IsMaximalTorus (T := (CommGroupScheme.baseChange (Spec.map a)).obj T)
    ((baseChange (Spec.map a)).map i) at h
  rwa [ha] at h


/-- The general relative torus-rigidity statement implies the unchanged split
field isogeny-uniqueness statement. -/
def SplitIsogenyRigidityReductionStatement : Prop :=
  ReductiveIsogenyTorusRigidityStatement.{u} → SplitIsogenyUniquenessStatement.{u}

/-- Full characters identify torus restrictions; relative rigidity supplies
local conjugators, which descend in the supplied actual adjoint torus. -/
theorem splitIsogenyRigidityReduction : SplitIsogenyRigidityReductionStatement.{u} := by
  intro hr
  apply splitIsogenyUniqueness_of_conjugatorExistence
  intro k _ G G' A hG T T' T'_ad hT i i' q j π h hi hi' φ₁ φ₂ t₁ t₂
    hφ₁ hφ₂ ht₁ ht₂ hchar
  have hG' := h.isAdjointQuotient.isConnectedReductive
  let := hG.smooth
  let := hG.isAffineHom
  let := hG'.smooth
  let := hG'.isAffineHom
  have ht : t₁ = t₂ := h.sourceMaximal.1.1.hom_ext_of_characters hchar
  have hrest : i ≫ φ₂ = i ≫ φ₁ := by rw [ht₁, ht₂, ht]
  have hrig := hr (Spec (CommRingCat.of k)) G G' hG.isReductive hG'.isReductive
    T T' i i' (RelativeTorus.IsTorus.of_isSplitTorus hT) hi.2.1
    hi.isFibrewiseMaximalTorus
    (RelativeTorus.IsTorus.of_isSplitTorus h.sourceMaximal.1.1) hi'.2.1
    hi'.isFibrewiseMaximalTorus φ₂ φ₁ hφ₂ hφ₁
    ⟨CommGroupScheme.groupHom t₂, ht₂⟩ ⟨CommGroupScheme.groupHom t₁, ht₁⟩
  obtain ⟨hlocal, hcentral⟩ := hrig
  obtain ⟨𝒰, h𝒰⟩ := hlocal.mp hrest
  choose t ht using h𝒰
  apply h.exists_basePoint_of_local_conjugates φ₂ φ₁ 𝒰 t ht
  intro V s t hs ht
  rw [mem_center]
  intro U a z
  change (a ≫ ((s ≫ i'.hom.hom)⁻¹ * (t ≫ i'.hom.hom))) * z =
    z * (a ≫ ((s ≫ i'.hom.hom)⁻¹ * (t ≫ i'.hom.hom)))
  simp only [MonObj.comp_mul, GrpObj.comp_inv]
  exact hcentral V s t hs ht U a z

end Langlands.GroupScheme
