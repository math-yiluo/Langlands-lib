import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanReduction
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Semisimple split groups have roots spanning a subgroup of finite index

The "only if" half of Milne Proposition 21.48, and the reduction of the split semisimplicity
criterion to its "if" half. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Submodule

/-- A submodule of infinite index in a finitely generated abelian group is annihilated by a
nonzero linear form: the quotient has a nonzero free part. -/
theorem exists_dual_ne_zero_of_infinite_quotient {X : Type*} [AddCommGroup X]
    [Module.Finite ℤ X] (R : Submodule ℤ X) (h : ¬ Finite (X ⧸ R)) :
    ∃ f : Module.Dual ℤ X, f ≠ 0 ∧ ∀ x ∈ R, f x = 0 := by
  classical
  let t := torsion ℤ (X ⧸ R)
  obtain ⟨q, hq⟩ : ∃ q : X ⧸ R, q ∉ t := by
    by_contra! hall
    exact h (Module.finite_of_fg_torsion _ fun q => (mem_torsion_iff q).1 (hall q))
  have : Module.Free ℤ ((X ⧸ R) ⧸ t) := Module.free_of_finite_type_torsion_free'
  have hq' : t.mkQ q ≠ 0 := by
    rwa [mkQ_apply, Ne, Quotient.mk_eq_zero]
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℤ hq'
  refine ⟨g ∘ₗ t.mkQ ∘ₗ R.mkQ, fun h0 => ?_, fun x hx => ?_⟩
  · obtain ⟨x, rfl⟩ := R.mkQ_surjective q
    exact hg (LinearMap.congr_fun h0 x)
  · simp [(Quotient.mk_eq_zero R).2 hx]

end Submodule

namespace Langlands.GroupScheme

/-- **Semisimple split groups have finite root index** (the "only if" half of Milne
Proposition 21.48). If `G` is semisimple over a field, `i : T ⟶ G` is a split closed torus and
`P` is a root datum of `i`, then the roots span a subgroup of finite index in the character
lattice. Otherwise a nonzero cocharacter `ν` annihilates every root, so `ν ≫ i` is central and
factors through the finite centre; a homomorphism from `𝔾_m` to a finite group scheme is trivial,
so `ν = 0`. -/
theorem IsSemisimple.finite_quotient_rootSpan {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G) [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ G} (hi : IsClosedSubgroup i) {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P) :
    Finite (characterLattice T ⧸ P.rootSpan ℤ) := by
  classical
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  by_contra hinf
  obtain ⟨f, hf0, hf⟩ := (P.rootSpan ℤ).exists_dual_ne_zero_of_infinite_quotient hinf
  let e : cocharacterLattice T ≃ₗ[ℤ] Module.Dual ℤ (characterLattice T) :=
    P.flip.toLinearMap.toPerfPair
  set ν := e.symm f with hν
  have hpair : ∀ α ∈ relativeRoots i, latticePairing T α ν = 0 := by
    intro α hα
    rw [relativeRoots_eq_roots, ← hP.2.1] at hα
    have h1 : e ν α = f α := by rw [hν, e.apply_symm_apply]
    rw [← hP.1]
    exact h1.trans (hf α (Submodule.subset_span hα))
  have hν0 : ν ≠ 0 := by
    intro h0
    apply hf0
    rw [← e.apply_symm_apply f, ← hν, h0, map_zero]
  have := hG.isConnectedReductive.smooth
  have := hG.isConnectedReductive.connectedSpace
  have hc := rootAnnihilatorCentrality k G T hT i ν hpair
  have hc0 := rootAnnihilatorCentrality k G T hT i 0 fun α _ => map_zero _
  obtain ⟨Z, z, hz, hfin⟩ := hG.hasFiniteCenter
  have hr := hz.isRepresentedBy
  have ha := hr.liftOfLE_comp _ ((isCentral_iff_range_le_center _).1 hc)
  have hb := hr.liftOfLE_comp _ ((isCentral_iff_range_le_center _).1 hc0)
  have hgm : IsSplitTorus (Gm (Spec (CommRingCat.of k))).toGrp := isSplitTorus_gm
  have := hgm.smooth
  have := hgm.isAffineHom
  have := hgm.connectedSpace
  let q : Z ⟶ Grp.trivial (Over (Spec (CommRingCat.of k))) := default
  have : IsFinite q.hom.hom.left := by
    have hw : q.hom.hom.left = Z.X.hom :=
      (Category.comp_id _).symm.trans (Over.w q.hom.hom)
    rw [hw]
    exact hfin
  have hab := finiteHom_cancel q (a := hr.liftOfLE _ ((isCentral_iff_range_le_center _).1 hc))
    (b := hr.liftOfLE _ ((isCentral_iff_range_le_center _).1 hc0)) (Subsingleton.elim _ _)
  have hi' : CommGroupScheme.groupHom ν ≫ i = CommGroupScheme.groupHom 0 ≫ i := by
    rw [← ha, ← hb, hab]
  have : IsClosedImmersion i.hom.hom.left := hi
  have hl : (CommGroupScheme.groupHom ν).hom.hom.left =
      (CommGroupScheme.groupHom (0 : cocharacterLattice T)).hom.hom.left := by
    rw [← cancel_mono i.hom.hom.left]
    exact congrArg (fun φ => φ.hom.hom.left) hi'
  have hg : CommGroupScheme.groupHom ν = CommGroupScheme.groupHom 0 := by
    apply Grp.hom_ext
    exact Over.OverMorphism.ext hl
  exact hν0 (congrArg Additive.ofMul hg)

/-- **Finite root index implies semisimplicity** (the "if" half of Milne Proposition 21.48 with
Definition C.34). For a connected reductive group `G` over a field with a split maximal torus
`i : T ⟶ G` and a root datum `P` of `i`, if the roots span a subgroup of finite index in the
character lattice, then `G` is semisimple. -/
def SplitSemisimpleOfFiniteRootIndexStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P → Finite (characterLattice T ⧸ P.rootSpan ℤ) → IsSemisimple G

/-- The "if" half of Milne Proposition 21.48 gives its full root form: the "only if" half is
`IsSemisimple.finite_quotient_rootSpan`. -/
theorem splitSemisimpleRootSpan_of_finiteRootIndex
    (h : SplitSemisimpleOfFiniteRootIndexStatement.{u}) :
    SplitSemisimpleRootSpanStatement.{u} := by
  intro k _ G hG T hT i hi J P hP
  have := hG.isAffineHom
  exact ⟨fun hs => hs.finite_quotient_rootSpan hT hi.2.1 hP, h k G hG T hT i hi J P hP⟩

/-- The "if" half of Milne Proposition 21.48 gives the published split semisimplicity criterion
in both its root and coroot forms. -/
theorem splitSemisimpleRootDatum_of_finiteRootIndex
    (h : SplitSemisimpleOfFiniteRootIndexStatement.{u}) :
    SplitSemisimpleRootDatumStatement.{u} :=
  splitSemisimpleRootDatum_of_rootSpan (splitSemisimpleRootSpan_of_finiteRootIndex h)

end Langlands.GroupScheme
