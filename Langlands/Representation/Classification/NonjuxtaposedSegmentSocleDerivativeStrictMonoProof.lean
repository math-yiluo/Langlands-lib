import Langlands.Representation.Category.FiniteLengthHelpers
import Langlands.Representation.Classification.SegmentSocleDerivativesStatement
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Classification.NonjuxtaposedSegmentSocleConstituentLevelProof

/-!
# Strict monotonicity of the nonjuxtaposed highest derivative

The lattice form (e) of Zelevinsky 1980, Proposition 4.3, deduced from its
published constituent-level form (d), `nonjuxtaposedSegmentSocleConstituentLevel`.
If `K₁ < K₂` are subrepresentations of a product `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` of
supplied segment socles with no two segments juxtaposed, the order-`λ`
derivative maps of the two actual inclusions have strictly nested ranges.

The deduction is generic: an exact functor whose value on every irreducible
subquotient of a finite-length representation `A` is nonzero strictly preserves
the ranges of the inclusions of nested subrepresentations of `A`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.NonjuxtaposedStrictMono

open Derivative Mirabolic

universe uG uH uV uF

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- A surjective morphism of smooth representations transfers finite length
from its source to its target. -/
theorem hasFiniteLength_of_surjective {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B)
    (hf : Function.Surjective (SmoothRep.hom f)) (hA : A.HasFiniteLength) :
    B.HasFiniteLength :=
  IsFiniteLength.of_surjective hA
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom f)) hf

/-- The actual inclusion between the representations on two nested
subrepresentations. -/
def inclusion (A : SmoothRep.{0, uG, uV} ℂ G) {K₁ K₂ : Subrepresentation A.representation}
    (h : K₁ ≤ K₂) : SmoothRep.subrepresentation A K₁ ⟶ SmoothRep.subrepresentation A K₂ :=
  SmoothRep.ofHom
    { toLinearMap := Submodule.inclusion h
      isIntertwining' := fun g => by ext v; rfl }

/-- The inclusion of `K₁` followed by that of `K₂` is the inclusion of `K₁`. -/
theorem inclusion_comp_subtype (A : SmoothRep.{0, uG, uV} ℂ G)
    {K₁ K₂ : Subrepresentation A.representation} (h : K₁ ≤ K₂) :
    inclusion A h ≫ SmoothRep.subtype A K₂ = SmoothRep.subtype A K₁ :=
  rfl

/-- An exact functor sends the inclusion of a subrepresentation to an injective
morphism. -/
theorem map_subtype_injective {J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H}
    (hJ : MapsShortExactIntertwiners J) (A : SmoothRep.{0, uG, uV} ℂ G)
    (K : Subrepresentation A.representation) :
    Function.Injective (SmoothRep.hom (J.map (SmoothRep.subtype A K))) :=
  (hJ _ _ _ (SmoothRep.subtype A K) (SmoothRep.mkQ A K) (SmoothRep.subtype_injective A K)
    (SmoothRep.mkQ_surjective A K)
    ((Submodule.range_subtype _).trans (Submodule.ker_mkQ _).symm)).1

/-- An exact functor whose value on every irreducible subquotient of a
finite-length representation `A` is nonzero strictly preserves the ranges of
the actual inclusions of nested subrepresentations of `A`. -/
theorem range_map_subtype_lt {J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H}
    (hJ : MapsShortExactIntertwiners J) {A : SmoothRep.{0, uG, uV} ℂ G}
    (hA : A.HasFiniteLength)
    (hnz : ∀ ω : SmoothRep.{0, uG, uV} ℂ G, ω.IsIrreducible → SmoothRep.IsSubquotient ω A →
      Nontrivial (J.obj ω))
    {K₁ K₂ : Subrepresentation A.representation} (hlt : K₁ < K₂) :
    (SmoothRep.hom (J.map (SmoothRep.subtype A K₁))).range <
      (SmoothRep.hom (J.map (SmoothRep.subtype A K₂))).range := by
  -- The short exact sequence `K₁ → K₂ → K₂/K₁` of actual representations.
  let P := SmoothRep.subrepresentation A K₂
  let i : SmoothRep.subrepresentation A K₁ ⟶ P := inclusion A hlt.le
  let U : Subrepresentation P.representation := (SmoothRep.hom i).range
  let Q := SmoothRep.quotient P U
  let q : P ⟶ Q := SmoothRep.mkQ P U
  have hi : Function.Injective (SmoothRep.hom i) := Submodule.inclusion_injective hlt.le
  have hq : Function.Surjective (SmoothRep.hom q) := SmoothRep.mkQ_surjective P U
  have hex : LinearMap.range (SmoothRep.hom i).toLinearMap =
      LinearMap.ker (SmoothRep.hom q).toLinearMap :=
    (Submodule.ker_mkQ _).symm
  obtain ⟨-, hJex, hJq⟩ := hJ _ _ _ i q hi hq hex
  have hcomp : J.map (SmoothRep.subtype A K₁) = J.map i ≫ J.map (SmoothRep.subtype A K₂) := by
    rw [← J.map_comp, inclusion_comp_subtype]
  have happ : ∀ x, SmoothRep.hom (J.map (SmoothRep.subtype A K₁)) x =
      SmoothRep.hom (J.map (SmoothRep.subtype A K₂)) (SmoothRep.hom (J.map i) x) := by
    intro x
    rw [hcomp]
    rfl
  -- Monotonicity, from the factorization through `K₁ → K₂`.
  have hle : (SmoothRep.hom (J.map (SmoothRep.subtype A K₁))).range ≤
      (SmoothRep.hom (J.map (SmoothRep.subtype A K₂))).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨SmoothRep.hom (J.map i) x, (happ x).symm⟩
  refine lt_of_le_not_ge hle fun hge => ?_
  -- Equal ranges make the image of `K₁ → K₂` surjective, so `J (K₂/K₁) = 0`.
  have hJ₂ := map_subtype_injective hJ A K₂
  have hJi : Function.Surjective (SmoothRep.hom (J.map i)) := by
    intro y
    obtain ⟨x, hx⟩ := hge ⟨y, rfl⟩
    exact ⟨x, hJ₂ ((happ x).symm.trans hx)⟩
  have hQ0 : Subsingleton (J.obj Q) := by
    have hzero : ∀ z : J.obj Q, z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := hJq z
      obtain ⟨x, rfl⟩ := hJi w
      have hmem : SmoothRep.hom (J.map i) x ∈
          LinearMap.ker (SmoothRep.hom (J.map q)).toLinearMap := hJex ▸ ⟨x, rfl⟩
      exact LinearMap.mem_ker.mp hmem
    exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  -- `K₂/K₁` is nonzero and of finite length.
  obtain ⟨v, hv₂, hv₁⟩ := SetLike.exists_of_lt hlt
  have hQnt : Nontrivial Q := by
    refine ⟨⟨SmoothRep.hom q ⟨v, hv₂⟩, 0, fun h0 => hv₁ ?_⟩⟩
    have hmem := (LinearMap.mem_ker (f := (SmoothRep.hom q).toLinearMap)).mpr h0
    rw [← hex] at hmem
    obtain ⟨w, hw⟩ := hmem
    let w' : K₁.toSubmodule := w
    have hv : w'.1 = v := congrArg Subtype.val hw
    rw [← hv]
    exact w'.2
  have hPfl : P.HasFiniteLength :=
    Aubert.ZelevinskyHighestDerivative.hasFiniteLength_of_injective (SmoothRep.subtype A K₂) (SmoothRep.subtype_injective A K₂) hA
  have hQfl : Q.HasFiniteLength := hasFiniteLength_of_surjective q hq hPfl
  -- An irreducible quotient `σ` of `K₂/K₁` is an irreducible subquotient of `A`.
  obtain ⟨σ, hσ, r, hr⟩ := SegmentHeadSupport.exists_irreducible_quotient hQfl
  have hsub : SmoothRep.IsSubquotient σ A :=
    SmoothRep.isSubquotient_iff_exists.mpr
      ⟨P, SmoothRep.subtype A K₂, q ≫ r, SmoothRep.subtype_injective A K₂,
        by rw [SmoothRep.hom_comp]; exact hr.comp hq⟩
  have hσnt := hnz σ hσ hsub
  -- Exactness makes `J σ` a quotient of `J (K₂/K₁) = 0`.
  have hJr := LevelCalculus.map_surjective_of_exact hJ r hr
  obtain ⟨a, b, hab⟩ := hσnt.exists_pair_ne
  obtain ⟨a', rfl⟩ := hJr a
  obtain ⟨b', rfl⟩ := hJr b
  exact hab (congrArg _ (Subsingleton.elim a' b'))

end Generic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Irreducibility is part of the supplied segment-socle relation. -/
theorem isIrreducible_of_isSegmentSocle {Δ : T.Segment.{uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π) :
    letI := T.topology
    π.IsIrreducible := by
  obtain ⟨_, _, h⟩ := hπ
  exact h.1

/-- A product of supplied segment socles has finite length in every rank: in
positive rank by the published finite length of products of irreducible
factors, and on `GL_0` because the product is one-dimensional. -/
theorem hasFiniteLength_induced {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (hd : d.HasSegmentSocles) :
    letI := T.topology
    d.induced.HasFiniteLength := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : FiniteDimensional ℂ d.induced :=
      Module.finite_of_finrank_eq_succ (SegmentProductOrderedAssembly.finrank_zeroDatum d)
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower ℂ inferInstance, isArtinian_of_tower ℂ inferInstance⟩
  · exact irreducibleProductFiniteLength.{uF, max uF uV} F T n hn d.shape d.blocks
      (fun i => isIrreducible_of_isSegmentSocle F T (hd i))

end Langlands.Classification.NonjuxtaposedStrictMono

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The lattice form (e) of Zelevinsky 1980, Proposition 4.3: for
subrepresentations `K₁ < K₂` of a nonjuxtaposed product of supplied segment
socles, the order-`λ` derivative maps of the actual inclusions have strictly
nested ranges. -/
theorem nonjuxtaposedSegmentSocleDerivativeStrictMono :
    NonjuxtaposedSegmentSocleDerivativeStrictMono.{uF, uV} F T := by
  let _ := T.topology
  intro ψ n d hs hnj k hk hkl K₁ K₂ hlt
  exact NonjuxtaposedStrictMono.range_map_subtype_lt
    (Derivative.generalLinearDerivativeExactness.{uF, max uF uV} F T ψ n k hk)
    (NonjuxtaposedStrictMono.hasFiniteLength_induced F T d hs)
    (fun ω hω hsub =>
      (nonjuxtaposedSegmentSocleConstituentLevel.{uF, uV} F T
        ψ n d hs hnj k hk hkl ω hω hsub).1) hlt

end Langlands.Classification
