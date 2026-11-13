import Langlands.GroupScheme.Rational.StandardWeylElementaryChainStatement
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy
import Langlands.GroupScheme.Rational.StandardLeviConjugationProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Group.RelativeWeylElementaryChain

/-! # Proof of the factorization into elementary Weyl elements (Renard VI.5.4)

The relation `w ∈ W(L_I, L_J)` is transferred to the Coxeter system of the relative Weyl
group: it implies conjugation of the standard relative Weyl subgroups, it holds for every
element sending the simple roots of `I` bijectively and positively onto those of `J`, and
it holds from `I` to `I` on `W_I`. The chain is then produced by the Coxeter-group theorem
`Langlands.Group.RelativeWeylIndexing.hasElementaryChain`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- Conjugation by an element of a subgroup preserves it. -/
theorem subgroup_map_conj_eq_self_of_mem {H : Type*} [Group H] {K : Subgroup H} {g : H}
    (hg : g ∈ K) : K.map (MulAut.conj g : H →* H) = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.mul_mem (K.mul_mem hg hy) (K.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg, ?_⟩
    simp [mul_assoc]

section Bridge

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)

omit [Mono i.hom.hom.left] in
/-- If a lift `n` of a Weyl element carries `L_I` onto `L_J`, then conjugation by that
Weyl element carries `W_I` onto `W_J`, in membership form. -/
theorem mem_standardRelativeWeylGroup_conj_iff {I J : Finset (SimpleRoot i ν)}
    (n : normalizerPoints i)
    (hn : (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
      RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J)
    (g : relativeWeylGroup i) :
    g ∈ standardRelativeWeylGroup i ν (rootSet i ν J) ↔
      (QuotientGroup.mk n : relativeWeylGroup i)⁻¹ * g * QuotientGroup.mk n ∈
        standardRelativeWeylGroup i ν (rootSet i ν I) := by
  rw [mem_standardRelativeWeylGroup_iff, mem_standardRelativeWeylGroup_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm' : (m : RationalPoint k G.X) ∈ levi i ν J := hm
    rw [← hn] at hm'
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp hm'
    refine ⟨n⁻¹ * m * n, ?_, by simp⟩
    have hle' : (n : RationalPoint k G.X) * l * (n : RationalPoint k G.X)⁻¹ = m := by
      simpa [MulAut.conj_apply] using hle
    have he : ((n⁻¹ * m * n : normalizerPoints i) : RationalPoint k G.X) = l := by
      push_cast
      rw [← hle']
      group
    change ((n⁻¹ * m * n : normalizerPoints i) : RationalPoint k G.X) ∈ levi i ν I
    rw [he]
    exact hl
  · rintro ⟨m, hm, hme⟩
    refine ⟨n * m * n⁻¹, ?_, ?_⟩
    · change ((n * m * n⁻¹ : normalizerPoints i) : RationalPoint k G.X) ∈ levi i ν J
      rw [← hn]
      exact Subgroup.mem_map.mpr ⟨m, hm, by simp⟩
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hme]
      group

omit [Mono i.hom.hom.left] in
/-- Every element of `W_I` has a lift in `L_I`, which carries `L_I` onto itself. -/
theorem exists_levi_map_conj_self_of_mem {I : Finset (SimpleRoot i ν)}
    {x : relativeWeylGroup i} (hx : x ∈ standardRelativeWeylGroup i ν (rootSet i ν I)) :
    ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = x ∧
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
        RationalPoint k G.X →* RationalPoint k G.X) = levi i ν I := by
  obtain ⟨n, hn, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp hx
  exact ⟨n, rfl, subgroup_map_conj_eq_self_of_mem hn⟩

/-- In a Coxeter realization, a Weyl element sending the simple reflections of `I`
positively and bijectively onto those of `J` has a lift carrying `L_I` onto `L_J`. -/
theorem exists_levi_map_conj_of_simple_bijection
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {CM : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)}
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    {I J : Finset (SimpleRoot i ν)} {x : relativeWeylGroup i}
    (hpos : ∀ a ∈ I, cs.length x < cs.length (x * cs.simple a))
    (hinto : ∀ a ∈ I, ∃ b ∈ J, x * cs.simple a * x⁻¹ = cs.simple b)
    (honto : ∀ b ∈ J, ∃ a ∈ I, x * cs.simple a * x⁻¹ = cs.simple b) :
    ∃ n : normalizerPoints i, (QuotientGroup.mk n : relativeWeylGroup i) = x ∧
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
        RationalPoint k G.X →* RationalPoint k G.X) = levi i ν J := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨n, rfl, ?_⟩
  apply levi_map_conj_of_character_image i ν hG hi hν standardLeviConjugation J I n
  rw [← schemeWeylCharacterAction_mk]
  ext α
  constructor
  · rintro ⟨β, ⟨a, ha, rfl⟩, rfl⟩
    have ha' : a ∈ I := ha
    obtain ⟨b, hb, he⟩ := hinto a ha'
    exact ⟨b, hb, (h.root_eq_of_conj_simple _ a b ((h.2.2.1 _ a).mp (hpos a ha')) he).symm⟩
  · rintro ⟨b, hb, rfl⟩
    have hb' : b ∈ J := hb
    obtain ⟨a, ha, he⟩ := honto b hb'
    exact ⟨a.val, ⟨a, ha, rfl⟩,
      h.root_eq_of_conj_simple _ a b ((h.2.2.1 _ a).mp (hpos a ha)) he⟩

end Bridge

/-- **Renard VI.5.4, Lemma (Bernstein–Zelevinsky 1977, Lemma 2.17).** Every
`w ∈ W(L, M)` with `L ≠ G` is a product of elementary elements along a chain of
standard Levi subgroups from `L` to `M`. -/
theorem standardWeylElementaryChain : StandardWeylElementaryChainStatement.{u} := by
  intro k _ _ _ _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν conj WS WLM ell IsElementary IL IM ha w hw
  obtain ⟨hfinW, hfinB, CM, cs, h⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  have : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  have hWS : ∀ I, standardSubgroup cs I = WS I := fun I => h.2.2.2.2 I
  let R : Finset (SimpleRoot i ν) → Finset (SimpleRoot i ν) → relativeWeylGroup i → Prop :=
    fun I J x => x ∈ WLM I J
  have hR1 : ∀ I J x, R I J x →
      ∀ g, g ∈ standardSubgroup cs J ↔ x⁻¹ * g * x ∈ standardSubgroup cs I := by
    rintro I J x ⟨n, rfl, hn⟩ g
    rw [hWS, hWS]
    exact mem_standardRelativeWeylGroup_conj_iff i ν n hn g
  have hR2 : ∀ I J x, (∀ a ∈ I, cs.length x < cs.length (x * cs.simple a)) →
      (∀ a ∈ I, ∃ b ∈ J, x * cs.simple a * x⁻¹ = cs.simple b) →
      (∀ b ∈ J, ∃ a ∈ I, x * cs.simple a * x⁻¹ = cs.simple b) → R I J x :=
    fun I J x hpos hinto honto =>
      exists_levi_map_conj_of_simple_bijection i ν hG hi hν h hpos hinto honto
  have hR3 : ∀ I x, x ∈ standardSubgroup cs I → R I I x := by
    intro I x hx
    rw [hWS] at hx
    exact exists_levi_map_conj_self_of_mem i ν hx
  obtain ⟨m, Ls, ws, h0, hlast, hel, hprod⟩ :=
    hasElementaryChain cs R hR1 hR2 hR3 WS hWS ha hw
  refine ⟨m, Ls, ws, h0, hlast, fun j => ?_, hprod⟩
  obtain ⟨hR, S, hIS, hJS, hgS, hcard⟩ := hel j
  exact ⟨hR, S, parabolic_mono hG hi hν standardParabolicOrder hIS,
    parabolic_mono hG hi hν standardParabolicOrder hJS, hgS, hcard⟩

end Langlands.GroupScheme
