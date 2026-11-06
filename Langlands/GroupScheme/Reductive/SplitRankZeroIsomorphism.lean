import Langlands.GroupScheme.Reductive.SplitRankOneIsomorphismStatement
import Langlands.GroupScheme.Nilpotent.EmptyRoots
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Torus.CentralMaximalQuotientProof
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.BaseChangeReflection

/-! # Connected reductive groups without roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- **A connected reductive group without roots is its maximal torus.** Let `i : T ⟶ G` be a
maximal torus of a connected reductive group `G` over a field, with `T` split. If `i` has no
roots, then `i` is an isomorphism. -/
theorem IsConnectedReductive.isIso_of_roots_eq_empty
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsMaximalTorus i)
    (hroot : (haveI := hG.isAffineHom; roots i = ∅)) : IsIso i := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  -- With no roots, `T` is central in `G`.
  have hc : IsCentral i := isCentral_of_roots_eq_empty hT i hroot
  -- Over an algebraic closure, the base change of `i` is still a central maximal torus.
  let b := toAlgebraicClosure k
  have hcK : IsCentral ((GroupScheme.baseChange b).map i) := hc.baseChange b
  have hmK : IsMaximalTorus
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map i) :=
    centralMaximalTorusBaseChangeReduction normalSubgroupQuotient
      centralMaximalTorusQuotientStatement (noTorusBaseChangeReduction noTorusUnipotent)
      k (AlgebraicClosure k) G T i hc hi
  -- There a connected reductive group with a central maximal torus is that torus.
  have : IsIso ((GroupScheme.baseChange b).map i) :=
    hG.baseChange_toAlgebraicClosure.isIso_of_isCentral_of_isMaximalTorus noTorusUnipotent
      solvableTorusQuotient hcK hmK
  -- Field extensions are fpqc, so `i` itself is an isomorphism.
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  exact isIso_of_baseChange b i

/-- Two root data on the same lattices, matched by a reindexing of their roots, describe tori
with the same set of roots. -/
theorem roots_eq_of_isRootDatumOf_of_reindex
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G₁.X.hom]
    [IsAffineHom G₂.X.hom] {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂} {J₁ J₂ : Type*}
    {P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T)}
    {P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T)}
    (h₁ : IsRootDatumOf i₁ P₁) (h₂ : IsRootDatumOf i₂ P₂) (e : J₁ ≃ J₂)
    (hroot : ⇑P₂.root ∘ ⇑e = ⇑P₁.root) : roots i₂ = roots i₁ := by
  rw [← h₁.2.1, ← h₂.2.1, ← hroot, Set.range_comp, e.range_eq_univ, Set.image_univ]

/-- **The Isomorphism Theorem in semisimple rank zero, common torus.** If `i₁ : T ⟶ G₁` and
`i₂ : T ⟶ G₂` are maximal tori of connected reductive groups with the same split torus `T` and
`i₁` has no roots, and root data of `i₁` and `i₂` differ by a reindexing that matches their
roots, then there is an isomorphism `ψ : G₁ ≅ G₂` with `i₁ ≫ ψ.hom = i₂`. -/
theorem exists_iso_of_roots_eq_empty
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂} (hi₁ : IsMaximalTorus i₁)
    (hi₂ : IsMaximalTorus i₂) {J₁ J₂ : Type*}
    {P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T)}
    {P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T)}
    (hP₁ : haveI := hG₁.isAffineHom; IsRootDatumOf i₁ P₁)
    (hP₂ : haveI := hG₂.isAffineHom; IsRootDatumOf i₂ P₂) (e : J₁ ≃ J₂)
    (hroot : ⇑P₂.root ∘ ⇑e = ⇑P₁.root)
    (hempty : (haveI := hG₁.isAffineHom; roots i₁ = ∅)) :
    ∃ ψ : G₁ ≅ G₂, i₁ ≫ ψ.hom = i₂ := by
  have := hG₁.isAffineHom
  have := hG₂.isAffineHom
  have hempty₂ : roots i₂ = ∅ := by
    rw [roots_eq_of_isRootDatumOf_of_reindex hP₁ hP₂ e hroot]
    exact hempty
  have := hG₁.isIso_of_roots_eq_empty hT hi₁ hempty
  have := hG₂.isIso_of_roots_eq_empty hT hi₂ hempty₂
  exact ⟨(asIso i₁).symm ≪≫ asIso i₂, by simp⟩

end Langlands.GroupScheme
