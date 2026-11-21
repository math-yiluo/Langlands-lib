import Langlands.Geometry.Analytic.QuasiEtaleStabilityStatement
import Langlands.Geometry.Analytic.QuasiEtaleDomainLocality
import Langlands.Geometry.Analytic.QuasiEtaleDiagonalLocal
import Langlands.Geometry.Analytic.QuasiEtaleDomainIntersections
import Langlands.Geometry.Analytic.EtaleSectionsOpen
import Langlands.Geometry.Analytic.EtaleBaseChangeReduction
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof

/-! # Morphisms between quasi-étale spaces over `X`, from local domain–étale factorizations -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Cancellation of a monomorphism on the right: if `c ≫ m` is an analytic-domain embedding
and `m` is a monomorphism, then `c` is an analytic-domain embedding. The square with sides
`𝟙`, `c`, `c ≫ m` and `m` is a pullback because `m` is a monomorphism. -/
theorem IsAnalyticDomainEmbedding.of_comp_mono {A B C : LocalizedCategory.{u, v, w} (K := K)}
    {c : A ⟶ B} {m : B ⟶ C} [Mono m] (h : IsAnalyticDomainEmbedding (c ≫ m)) :
    IsAnalyticDomainEmbedding c := by
  have hsq : IsPullback (𝟙 A) c (c ≫ m) m := by
    apply IsPullback.mk'
    · simp
    · intro _ _ _ h₁ _
      simpa using h₁
    · intro T x y hxy
      exact ⟨x, Category.comp_id x, (cancel_mono m).1 (by simpa using hxy)⟩
  exact h.of_isPullback hsq

/-- Analytic-domain embeddings are monomorphisms. -/
theorem IsAnalyticDomainEmbedding.mono {A B : LocalizedCategory.{u, v, w} (K := K)}
    {j : A ⟶ B} (hj : IsAnalyticDomainEmbedding j) : Mono j := by
  obtain ⟨D, e, rfl⟩ := hj
  infer_instance

/-- The second projection of every pullback square along an étale arrow is étale: compare the
square with the pullback supplied by `localizedEtalePullbackBaseChange`. -/
private theorem etale_of_isPullback_localized {P A B X : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback p q f g) (hf : etale f) : etale q := by
  obtain ⟨_, _, _, hP, hq⟩ := localizedEtalePullbackBaseChange (K := K) f g hf
  exact etale_snd_of_isPullback hP h hq

/-- The local graph lemma. Let `w : W ⟶ X` be étale and let `P` be a pullback of `w` along
`g : Y ⟶ X`. Let `a : T ⟶ W` be an analytic-domain embedding, and let `h = k ≫ m : T ⟶ Y`
satisfy `a ≫ w = h ≫ g`, where `m : D ⟶ Y` is an analytic-domain embedding and
`m ≫ g = b ≫ u` for an analytic-domain embedding `b : D ⟶ U` and an étale `u : U ⟶ X`.
Then the graph `T ⟶ P` of `(a, h)` is an analytic-domain embedding. -/
theorem isAnalyticDomainEmbedding_graph
    {T W X Y D U P : LocalizedCategory.{u, v, v} (K := K)}
    {w : W ⟶ X} {g : Y ⟶ X} {pW : P ⟶ W} {pY : P ⟶ Y} (hP : IsPullback pW pY w g)
    (hw : etale w) {a : T ⟶ W} (ha : IsAnalyticDomainEmbedding a)
    {k : T ⟶ D} {m : D ⟶ Y} (hm : IsAnalyticDomainEmbedding m)
    {b : D ⟶ U} (hb : IsAnalyticDomainEmbedding b) {u : U ⟶ X} (hu : etale u)
    (hmb : m ≫ g = b ≫ u) (hak : a ≫ w = (k ≫ m) ≫ g) :
    IsAnalyticDomainEmbedding (hP.lift a (k ≫ m) hak) := by
  -- `Q = W ×_X U`, with both projections étale.
  let cQ := localizedEtalePullback w u hw
  have hQ : IsPullback cQ.1.fst cQ.1.snd w u := IsPullback.of_isLimit cQ.2
  have hqW : etale cQ.1.fst := etale_of_isPullback_localized hQ.flip hu
  have hqU : etale cQ.1.snd := etale_of_isPullback_localized hQ hw
  -- The map `ε = (a, k ≫ b) : T ⟶ Q`.
  have hεw : a ≫ w = (k ≫ b) ≫ u := by
    rw [hak, Category.assoc, Category.assoc, hmb]
  let ε : T ⟶ cQ.1.pt := hQ.lift a (k ≫ b) hεw
  -- `R = Q ×_W T`; `ε` is a section of `R ⟶ T` followed by `R ⟶ Q`.
  let cR := localizedEtalePullback cQ.1.fst a hqW
  have hR : IsPullback cR.1.fst cR.1.snd cQ.1.fst a := IsPullback.of_isLimit cR.2
  have hrT : etale cR.1.snd := etale_of_isPullback_localized hR hqW
  let s : T ⟶ cR.1.pt := hR.lift ε (𝟙 T) (by simp [ε])
  have hs : s ≫ cR.1.snd = 𝟙 T := hR.lift_snd _ _ _
  obtain ⟨V, hV, e, he⟩ := localizedEtaleSectionsOpen hrT hs
  have hsD : IsAnalyticDomainEmbedding s :=
    ⟨(presentationOf cR.1.pt).openDomain V hV, e, he.symm⟩
  have hrQ : IsAnalyticDomainEmbedding cR.1.fst := ha.of_isPullback hR.flip
  have hεs : s ≫ cR.1.fst = ε := hR.lift_fst _ _ _
  have hε : IsAnalyticDomainEmbedding ε := hεs ▸ hsD.comp hrQ
  -- `S = Q ×_U D`; `ε` factors through the analytic-domain embedding `S ⟶ Q`.
  let cS := localizedEtalePullback cQ.1.snd b hqU
  have hS : IsPullback cS.1.fst cS.1.snd cQ.1.snd b := IsPullback.of_isLimit cS.2
  have hsQ : IsAnalyticDomainEmbedding cS.1.fst := hb.of_isPullback hS.flip
  have : Mono cS.1.fst := hsQ.mono
  have hεU : ε ≫ cQ.1.snd = k ≫ b := hQ.lift_snd _ _ _
  let ε' : T ⟶ cS.1.pt := hS.lift ε k hεU
  have hε'₁ : ε' ≫ cS.1.fst = ε := hS.lift_fst _ _ _
  have hε'₂ : ε' ≫ cS.1.snd = k := hS.lift_snd _ _ _
  have hε' : IsAnalyticDomainEmbedding ε' := IsAnalyticDomainEmbedding.of_comp_mono (hε'₁ ▸ hε)
  -- The comparison `t : S ⟶ P` is the base change of `m` along `pY`.
  have htw : (cS.1.fst ≫ cQ.1.fst) ≫ w = (cS.1.snd ≫ m) ≫ g := by
    rw [Category.assoc, hQ.w, ← Category.assoc, hS.w, Category.assoc, Category.assoc, hmb]
  let t : cS.1.pt ⟶ P := hP.lift (cS.1.fst ≫ cQ.1.fst) (cS.1.snd ≫ m) htw
  have ht₁ : t ≫ pW = cS.1.fst ≫ cQ.1.fst := hP.lift_fst _ _ _
  have ht₂ : t ≫ pY = cS.1.snd ≫ m := hP.lift_snd _ _ _
  have htsq : IsPullback cS.1.snd t m pY := by
    apply IsPullback.mk'
    · exact ht₂.symm
    · intro Z φ φ' h₁ h₂
      apply hS.hom_ext
      · apply hQ.hom_ext
        · have h := congrArg (· ≫ pW) h₂
          simpa only [Category.assoc, ht₁] using h
        · rw [Category.assoc, Category.assoc, hS.w, ← Category.assoc, h₁, Category.assoc]
      · exact h₁
    · intro Z x y hxy
      have h₀ : (y ≫ pW) ≫ w = (x ≫ b) ≫ u := by
        rw [Category.assoc, hP.w, ← Category.assoc, ← hxy, Category.assoc, Category.assoc, hmb]
      let l₀ : Z ⟶ cQ.1.pt := hQ.lift (y ≫ pW) (x ≫ b) h₀
      let l : Z ⟶ cS.1.pt := hS.lift l₀ x (hQ.lift_snd _ _ _)
      have hl₁ : l ≫ cS.1.fst = l₀ := hS.lift_fst _ _ _
      have hl₂ : l ≫ cS.1.snd = x := hS.lift_snd _ _ _
      refine ⟨l, hl₂, ?_⟩
      apply hP.hom_ext
      · rw [Category.assoc, ht₁, ← Category.assoc, hl₁]
        exact hQ.lift_fst _ _ _
      · rw [Category.assoc, ht₂, ← Category.assoc, hl₂, hxy]
  have ht : IsAnalyticDomainEmbedding t := hm.of_isPullback htsq
  have hγ : hP.lift a (k ≫ m) hak = ε' ≫ t := by
    apply hP.hom_ext
    · rw [hP.lift_fst, Category.assoc, ht₁, ← Category.assoc, hε'₁]
      exact (hQ.lift_fst _ _ _).symm
    · rw [hP.lift_snd, Category.assoc, ht₂, ← Category.assoc, hε'₂]
  rw [hγ]
  exact hε'.comp ht

/-- Local graph factorization. Let `g : Y ⟶ X`, and let `h : T ⟶ Y` be such that `h ≫ g`
has a domain–étale factorization. If `h` factors through an analytic-domain embedding
`m : D ⟶ Y` for which `m ≫ g` has a domain–étale factorization, then `h` has a domain–étale
factorization, through the graph of `h` into the pullback of the étale envelope of `h ≫ g`. -/
theorem HasDomainEtaleFactorization.of_comp_of_factor
    {T Y X D : LocalizedCategory.{u, v, v} (K := K)} {h : T ⟶ Y} {g : Y ⟶ X}
    (hT : HasDomainEtaleFactorization (h ≫ g)) {k : T ⟶ D} {m : D ⟶ Y}
    (hm : IsAnalyticDomainEmbedding m) (hkm : k ≫ m = h)
    (hD : HasDomainEtaleFactorization (m ≫ g)) :
    HasDomainEtaleFactorization h := by
  obtain ⟨W, a, w, ha, hw, haw⟩ := hT
  obtain ⟨U, b, u, hb, hu, hbu⟩ := hD
  subst hkm
  let cP := localizedEtalePullback w g hw
  have hP : IsPullback cP.1.fst cP.1.snd w g := IsPullback.of_isLimit cP.2
  have hpY : etale cP.1.snd := etale_of_isPullback_localized hP hw
  exact ⟨cP.1.pt, hP.lift a (k ≫ m) haw, cP.1.snd,
    isAnalyticDomainEmbedding_graph hP hw ha hm hb hu hbu.symm haw, hpY, hP.lift_snd _ _ _⟩

set_option linter.defProp false in
/-- Reduction (Berkovich 1994, Lemma 3.1(ii)): if every quasi-étale arrow of the localized
category has local domain–étale factorizations through every source point, then for
quasi-étale `g : Y ⟶ X` and `f ≫ g : Z ⟶ X` the arrow `f : Z ⟶ Y` is quasi-étale.
The premise is the body of the proposition `QuasiEtaleLocalDomainFactorizationsStatement`
staged in Task 7910. It is declared with `def` (its type is a proposition) so that it can be
recorded as a supporting definition artifact. -/
def quasiEtaleOverMorphism_of_localDomainFactorizations
    (hloc : ∀ {U X : LocalizedCategory.{u, v, v} (K := K)} (f : U ⟶ X),
      quasiEtale f → HasLocalDomainEtaleFactorizations f) :
    QuasiEtaleOverMorphismStatement.{u, v} K := by
  refine ⟨fun {Z Y X} f g hg hfg => ?_⟩
  apply HasLocalDomainEtaleFactorizations.quasiEtale
  intro z
  obtain ⟨C, hCf, hCn, hC⟩ := hloc (f ≫ g) hfg z
  obtain ⟨C', hC'f, hC'n, hC'⟩ := hloc g hg (localizedSpaceFunctor.map f z)
  let F : (presentationOf Z).AnalyticDomain × (presentationOf Y).AnalyticDomain →
      (presentationOf Z).AnalyticDomain := fun p => p.1 ⊓ domainPreimage f p.2
  refine ⟨F '' (C ×ˢ C'), (hCf.prod hC'f).image F, ?_, ?_⟩
  · have hpre : localizedSpaceFunctor.map f ⁻¹' (⋃ D ∈ C', D.carrier) ∈ 𝓝 z :=
      (localizedSpaceFunctor.map f).hom.continuous.continuousAt.preimage_mem_nhds hC'n
    refine Filter.mem_of_superset (Filter.inter_mem hCn hpre) ?_
    rintro x ⟨hx₁, hx₂⟩
    obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.1 hx₁
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 (Set.mem_preimage.1 hx₂)
    exact Set.mem_iUnion₂.2 ⟨F (E, D), ⟨(E, D), ⟨hE, hD⟩, rfl⟩, hxE, hxD⟩
  · rintro _ ⟨⟨E, D⟩, ⟨hE, hD⟩, rfl⟩
    refine ⟨⟨(hC E hE).1, (hC' D hD).1⟩, ?_⟩
    have hT : HasDomainEtaleFactorization
        ((domainι Z (E ⊓ domainPreimage f D) ≫ f) ≫ g) := by
      rw [Category.assoc]
      exact (hC E hE).2.of_domain_le inf_le_left
    refine hT.of_comp_of_factor (isAnalyticDomainEmbedding_domainι Y D)
      (k := domainOrderMap (inf_le_right : E ⊓ domainPreimage f D ≤ domainPreimage f D) ≫
        domainPreimageMap f D) ?_ (hC' D hD).2
    simp only [Category.assoc, domainPreimageMap_comp_inclusion,
      domainOrderMap_comp_inclusion_assoc]

end Langlands.Analytic.SaturatedAtlasPresentation
