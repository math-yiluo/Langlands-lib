import Langlands.Representation.Classification.SegmentSocleJacquetStatement
import Langlands.Representation.Classification.SegmentFullJacquetStatement
import Langlands.Representation.Classification.SegmentConstituentStatement
import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.Classification.SegmentTensorStabilizerProof
import Langlands.Representation.Classification.IrreducibleProductEmbedding
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.Parabolic.RefinementJacquetTransitivityProof
import Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Classification.SegmentInductionAdmissibilityProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Classification.RegularLanglandsHeadReduction
import Langlands.Representation.Tensor.FiniteProperties

/-! Conditional reduction of Zelevinsky 1980, Proposition 3.4. -/

noncomputable section

namespace Langlands.Classification.SegmentSocleJacquetReduction

open GeneralLinear Geometric CuspidalSupport CategoryTheory

universe uF uV

section Combinatorics

/-- A block shape associated with the uniform shape `(r, …, r)` has only blocks of
size `r`. -/
theorem size_eq_of_levisAssociated_uniform {F : Type*} [Field F] {m r : ℕ} (hr : 0 < r)
    {D : BlockShape (m * r)}
    (h : LevisAssociated (F := F) (BlockShape.uniform m r hr) D) (j : Fin D.length) :
    D.size j = r := by
  obtain ⟨⟨w, hw⟩⟩ := h
  obtain ⟨i, rfl⟩ := TotalConjugatingCount.blockMap_surjective hw j
  rw [TotalConjugatingCount.size_blockMap hw i]
  rfl

/-- If all flattened blocks have size `r`, so do all inner blocks of the refinement. -/
theorem refinement_size_eq {n r : ℕ} {C : BlockShape n} (S : BlockRefinement C)
    (h : ∀ j, (C.flatten S).size j = r) (i : Fin C.length) (j : Fin (S i).length) :
    (S i).size j = r := by
  rw [← C.flatten_size_flattenBlockEquiv S ⟨i, j⟩]
  exact h _

/-- A block shape of `k` whose blocks all have size `r` has `k = length * r`. -/
theorem eq_length_mul_of_size_eq {k r : ℕ} (D : BlockShape k) (h : ∀ j, D.size j = r) :
    k = D.length * r := by
  calc k = ∑ j, D.size j := D.sum_eq.symm
    _ = D.length * r := by simp [h]

/-- A block shape of `q r` whose blocks all have size `r` is the uniform shape. -/
theorem eq_uniform_of_size_eq {q r : ℕ} (hr : 0 < r) (D : BlockShape (q * r))
    (h : ∀ j, D.size j = r) : D = BlockShape.uniform q r hr := by
  obtain ⟨l, s, hs, hsum⟩ := D
  have hl : l = q := by
    have := eq_length_mul_of_size_eq ⟨l, s, hs, hsum⟩ h
    exact (Nat.eq_of_mul_eq_mul_right hr this).symm
  subst hl
  have hs' : s = fun _ => r := funext h
  subst hs'
  rfl

/-- Two block shapes of `k` whose blocks all have the same positive size are equal. -/
theorem blockShape_eq_of_size_eq {k r : ℕ} (hr : 0 < r) (D D' : BlockShape k)
    (h : ∀ j, D.size j = r) (h' : ∀ j, D'.size j = r) : D = D' := by
  obtain ⟨l, s, hs, hsum⟩ := D
  obtain ⟨l', s', hs', hsum'⟩ := D'
  have hl : l = l' := by
    have e := eq_length_mul_of_size_eq ⟨l, s, hs, hsum⟩ h
    have e' := eq_length_mul_of_size_eq ⟨l', s', hs', hsum'⟩ h'
    exact Nat.eq_of_mul_eq_mul_right hr (e.symm.trans e')
  subst hl
  have hss : s = s' := funext fun j => (h j).trans (h' j).symm
  subst hss
  rfl

/-- Two refinements whose flattened blocks all have the same positive size are equal. -/
theorem refinement_eq_of_size_eq {n r : ℕ} (hr : 0 < r) {C : BlockShape n}
    (S S' : BlockRefinement C) (h : ∀ j, (C.flatten S).size j = r)
    (h' : ∀ j, (C.flatten S').size j = r) : S = S' :=
  funext fun i => blockShape_eq_of_size_eq hr _ _ (refinement_size_eq S h i)
    (refinement_size_eq S' h' i)

end Combinatorics

section Pullback

universe uR uG uW

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Pull an injection back along a surjection: some subrepresentation of the source
of the surjection maps onto the source of the injection. -/
theorem exists_injective_surjective_of_pullback {Z R Y : SmoothRep.{uR, uG, uW} k G}
    (f : Z ⟶ R) (hf : Function.Surjective (SmoothRep.hom f))
    (i : Y ⟶ R) (hi : Function.Injective (SmoothRep.hom i)) :
    ∃ (K : SmoothRep.{uR, uG, uW} k G) (a : K ⟶ Z) (g : K ⟶ Y),
      Function.Injective (SmoothRep.hom a) ∧ Function.Surjective (SmoothRep.hom g) := by
  classical
  let fl := (SmoothRep.hom f).toLinearMap
  let il := (SmoothRep.hom i).toLinearMap
  let Kc : Subrepresentation Z.representation :=
    { toSubmodule := (LinearMap.range il).comap fl
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨y, hy⟩ := hv
        refine ⟨Y.representation g y, ?_⟩
        change SmoothRep.hom i (Y.representation g y) =
          SmoothRep.hom f (Z.representation g v)
        rw [(SmoothRep.hom i).isIntertwining, (SmoothRep.hom f).isIntertwining]
        exact congrArg (R.representation g) hy }
  let e := LinearEquiv.ofInjective il hi
  have he : ∀ z : LinearMap.range il, il (e.symm z) = z := fun z =>
    (LinearEquiv.ofInjective_apply (f := il) (h := hi) (e.symm z)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply z))
  let gl : Kc.toSubmodule →ₗ[k] Y :=
    e.symm.toLinearMap ∘ₗ fl.restrict (p := Kc.toSubmodule) (q := LinearMap.range il)
      (fun _ hx => hx)
  have hgl : ∀ x : Kc.toSubmodule, il (gl x) = fl x := fun x => he _
  let K := SmoothRep.subrepresentation Z Kc
  let g : K.representation.IntertwiningMap Y.representation :=
    LinearMap.intertwiningMap_of_isIntertwiningMap K.representation Y.representation gl
      (fun h x => by
        apply hi
        refine (hgl _).trans ?_
        change fl (Z.representation h x.val) = SmoothRep.hom i (Y.representation h (gl x))
        rw [(SmoothRep.hom i).isIntertwining]
        refine Eq.trans ?_ (congrArg (R.representation h) (hgl x).symm)
        exact Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) h x.val)
  refine ⟨K, SmoothRep.subtype Z Kc, SmoothRep.ofHom g, SmoothRep.subtype_injective Z Kc, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := hf (SmoothRep.hom i y)
  refine ⟨⟨z, y, hz.symm⟩, ?_⟩
  apply hi
  change il (gl _) = il y
  rw [hgl]
  exact hz

end Pullback

section PullbackMap

variable {G H : Type*} [Monoid G] [Monoid H] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- An intertwiner remains an intertwiner after pulling both actions back along a
monoid homomorphism. -/
def compMap {ρ : Representation ℂ H V} {σ : Representation ℂ H W} (φ : G →* H)
    (f : ρ.IntertwiningMap σ) : Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := f.isIntertwining' (φ g)

@[simp]
theorem compMap_apply {ρ : Representation ℂ H V} {σ : Representation ℂ H W} (φ : G →* H)
    (f : ρ.IntertwiningMap σ) (v : V) : compMap φ f v = f v := rfl

end PullbackMap

section Socle

universe uG uX

variable {G : Type uG} [Group G] {V W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- Lift an intertwiner through an injective intertwiner whose range contains its
values. -/
theorem exists_lift_of_mem_range {ρ : Representation ℂ G V} {σ : Representation ℂ G X}
    {τ : Representation ℂ G W} (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι)
    (j : τ.IntertwiningMap ρ) (h : ∀ w, j w ∈ LinearMap.range ι.toLinearMap) :
    ∃ ψ : τ.IntertwiningMap σ, ∀ w, ι (ψ w) = j w := by
  let il := ι.toLinearMap
  let e := LinearEquiv.ofInjective il hι
  have he : ∀ z : LinearMap.range il, il (e.symm z) = z := fun z =>
    (LinearEquiv.ofInjective_apply (f := il) (h := hι) (e.symm z)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply z))
  let ψl : W →ₗ[ℂ] X := e.symm.toLinearMap ∘ₗ j.toLinearMap.codRestrict _ h
  have hψ : ∀ w, ι (ψl w) = j w := fun w => he _
  refine ⟨LinearMap.intertwiningMap_of_isIntertwiningMap τ σ ψl (fun g w => ?_), hψ⟩
  apply hι
  refine (hψ _).trans ?_
  rw [j.isIntertwining, ι.isIntertwining, hψ]

/-- Inside a representation of finite length with irreducible socle `π`, the socle
lies in the range of every injective intertwiner from a nonzero representation. -/
theorem exists_mem_range_of_isIrreducibleSocle {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} (hs : Classification.IsIrreducibleSocle ρ π)
    (hfin : IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule) {σ : Representation ℂ G X}
    (hX : Nontrivial X) (ι : σ.IntertwiningMap ρ) (hι : Function.Injective ι) :
    ∃ j : π.IntertwiningMap ρ, Function.Injective j ∧
      ∀ w, j w ∈ LinearMap.range ι.toLinearMap := by
  obtain ⟨-, j, hj, huniq⟩ := hs
  refine ⟨j, hj, fun w => ?_⟩
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have hN : e ι.range ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have hmem : ι x ∈ ι.range := ⟨x, rfl⟩
    have h0 : ι.range = ⊥ := e.injective (hbot.trans e.map_bot.symm)
    rw [h0] at hmem
    exact hx (hι ((hmem : ι x = 0).trans (map_zero ι).symm))
  obtain ⟨a, ha, hle⟩ := (eq_bot_or_exists_atom_le (e ι.range)).resolve_left hN
  let S := e.symm a
  have hS : IsAtom S := (e.symm.isAtom_iff a).mpr ha
  have hSle : S ≤ ι.range := by
    have := e.symm.monotone hle
    rwa [e.symm_apply_apply] at this
  let jS : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hjS : Function.Injective jS := Subtype.val_injective
  have hrange := huniq _ S.toRepresentation
    (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS) jS hjS
  have hw : j w ∈ LinearMap.range jS.toLinearMap := by
    rw [hrange]
    exact ⟨w, rfl⟩
  obtain ⟨s, hs⟩ := hw
  rw [← hs]
  exact hSle s.property

end Socle

section CuspidalBlocks

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The normalized refined Jacquet module of `X` along `S`, pulled back to the Levi of
the flattened shape `C.flatten S` along the flattened Levi equivalence. -/
def flattenedRefinedJacquet {n : ℕ} (C : BlockShape n) (S : BlockRefinement C) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier) →
      SmoothRep.{0, uF, uV} ℂ ((C.flatten S).Levi F.Carrier) :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  fun X => SmoothRep.of
    ((T.normalizedRefinedJacquet C S X.representation).comp
      (flattenedLeviEquiv F.Carrier C S).toMonoidHom)
    (isSmooth_comp _ (flattenedLeviEquivContinuous F.Carrier C S).continuous
      (T.isSmooth_normalizedRefinedJacquet C S X.isSmooth))

/-- The refined Jacquet map between pulled-back refined Jacquet modules. -/
def flattenedRefinedJacquetMap {n : ℕ} (C : BlockShape n) (S : BlockRefinement C) :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)}, (X ⟶ Y) →
      (flattenedRefinedJacquet T C S X ⟶ flattenedRefinedJacquet T C S Y) :=
  letI := T.topology
  fun f => SmoothRep.ofHom
    (compMap (flattenedLeviEquiv F.Carrier C S).toMonoidHom
      (T.normalizedRefinedJacquetMap C S (SmoothRep.hom f)))

theorem flattenedRefinedJacquetMap_injective {n : ℕ} (C : BlockShape n)
    (S : BlockRefinement C) :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)} (f : X ⟶ Y),
      Function.Injective (SmoothRep.hom f) →
        Function.Injective (SmoothRep.hom (flattenedRefinedJacquetMap T C S f)) := by
  let := T.topology
  intro X Y f hf
  exact RefinedJacquetLengthProof.map_injective T C S (SmoothRep.hom f) Y.isSmooth hf

theorem flattenedRefinedJacquetMap_surjective {n : ℕ} (C : BlockShape n)
    (S : BlockRefinement C) :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (C.Levi F.Carrier)} (f : X ⟶ Y),
      Function.Surjective (SmoothRep.hom f) →
        Function.Surjective (SmoothRep.hom (flattenedRefinedJacquetMap T C S f)) := by
  let := T.topology
  intro X Y f hf x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective Y.representation (refinedUnipotent F.Carrier C S) x
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨refinedJacquetMk C S X.representation v, rfl⟩

/-- The flattened Jacquet quotient as a morphism of smooth representations. -/
def flattenedQuotient {n : ℕ} (C : BlockShape n) (S : BlockRefinement C) :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      (T.normalizedJacquetFunctor (C.flatten S)).obj π ⟶
        flattenedRefinedJacquet T C S ((T.normalizedJacquetFunctor C).obj π) :=
  letI := T.topology
  fun π => SmoothRep.ofHom (Parabolic.flattenedJacquetQuotientMap T C S π.representation)

theorem flattenedQuotient_surjective {n : ℕ} (C : BlockShape n) (S : BlockRefinement C) :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      Function.Surjective (SmoothRep.hom (flattenedQuotient T C S π)) := by
  let := T.topology
  intro π
  exact MinimalJacquet.flattenJacquetMap_surjective T C S π.representation

/-- **Lemma K.** Let `π` embed in the normalized induction of a quasicuspidal `ρ` from the
uniform shape `(r, …, r)`. Every nonzero subquotient `X` of a normalized Jacquet module
`r_C(π)` has a block refinement `S` of `C` into blocks of size `r` with nonzero refined
Jacquet module. -/
theorem exists_refinement_size_eq {m r : ℕ} (hr : 0 < r)
    (hH2 : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T (m * r)) :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ ((BlockShape.uniform m r hr).Levi F.Carrier)),
      IsLeviQuasicuspidal (BlockShape.uniform m r hr) ρ.representation →
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
      (j : π ⟶ (T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj ρ),
      Function.Injective (SmoothRep.hom j) →
    ∀ (C : BlockShape (m * r)) (P X : SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F.Carrier))
      (i : P ⟶ (T.normalizedJacquetFunctor C).obj π) (s : P ⟶ X),
      Function.Injective (SmoothRep.hom i) → Function.Surjective (SmoothRep.hom s) →
      Nontrivial X →
      ∃ S : BlockRefinement C, (∀ k, (C.flatten S).size k = r) ∧
        Nontrivial (RefinedJacquetModule C S X.representation) := by
  let := T.topology
  intro ρ hρ π j hj C P X i s hi hs hX
  obtain ⟨S, hne, hcusp⟩ := minimalNonzeroRefinedJacquet.{uF, max uF uV} F T _ C X hX
  rw [BlockShape.leviRefinementEquiv_flatten] at hcusp
  refine ⟨S, fun k => ?_, hne⟩
  let Jf := T.normalizedJacquetFunctor (C.flatten S)
  obtain ⟨K, a, g, ha, hg⟩ := exists_injective_surjective_of_pullback
    (flattenedQuotient T C S π) (flattenedQuotient_surjective T C S π)
    (flattenedRefinedJacquetMap T C S i) (flattenedRefinedJacquetMap_injective T C S i hi)
  have hsub : SmoothRep.IsSubquotient (flattenedRefinedJacquet T C S X)
      (Jf.obj ((T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj ρ)) := by
    refine SmoothRep.isSubquotient_iff_exists.mpr
      ⟨K, a ≫ Jf.map j, g ≫ flattenedRefinedJacquetMap T C S s, ?_, ?_⟩
    · rw [SmoothRep.hom_comp]
      exact (JacquetDetectingFamilyLengthProof.jacquet_injective T (C.flatten S)
        (SmoothRep.hom j) hj).comp ha
    · rw [SmoothRep.hom_comp]
      exact (flattenedRefinedJacquetMap_surjective T C S s hs).comp hg
  have hassoc : LevisAssociated (F := F.Carrier) (BlockShape.uniform m r hr) (C.flatten S) := by
    by_contra hna
    have h0 := hH2 _ (C.flatten S) ρ hρ hna (flattenedRefinedJacquet T C S X) hsub hcusp
    exact not_subsingleton (RefinedJacquetModule C S X.representation) h0
  exact size_eq_of_levisAssociated_uniform hr hassoc k

end CuspidalBlocks

section Segment

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- The segment induction is normalized parabolic induction of the external tensor
product of its block factors. -/
theorem segmentInduced_eq {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    T.segmentInduced A m hr =
      (T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj
        (FiniteTensor.externalSmoothObject (T.segmentFactors A m hr)) :=
  rfl

/-- The external tensor product of the block factors of a segment is quasicuspidal. -/
theorem segmentFactors_isLeviQuasicuspidal {r : ℕ} (m : ℕ) (hm : 0 < m) (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    IsLeviQuasicuspidal (BlockShape.uniform m r hr)
      (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)).representation :=
  (Classification.segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A).2.2

/-- **Clause 1 of Ze80 3.4.** For an irreducible subrepresentation `π` of the segment
induction, the normalized Jacquet module along `(l, n - l)` vanishes unless the
cuspidal rank divides `l`. -/
theorem jacquet_ofPair_subsingleton
    (hH2 : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n) :
    letI := T.topology
    ∀ (Δ : Segment.{uV, uF} T)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSubrepresentation Δ π →
      ∀ (l : ℕ) (hl : 0 < l) (hln : l < Δ.degree), ¬ Δ.rank ∣ l →
        Subsingleton ((T.normalizedJacquetFunctor
          (BlockShape.ofPair l (Δ.degree - l) hl (Nat.sub_pos_of_lt hln)
            (Nat.add_sub_of_le hln.le))).obj π) := by
  let := T.topology
  intro Δ π ⟨A, _, _, j, hj⟩ l hl hln hdvd
  let C := BlockShape.ofPair l (Δ.degree - l) hl (Nat.sub_pos_of_lt hln)
    (Nat.add_sub_of_le hln.le)
  rw [← not_nontrivial_iff_subsingleton]
  intro hJ
  obtain ⟨S, hS, -⟩ := exists_refinement_size_eq T Δ.rank_pos (hH2 _)
    (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj Δ.length Δ.rank_pos))
    (segmentFactors_isLeviQuasicuspidal T Δ.length Δ.length_pos Δ.rank_pos A)
    π (SmoothRep.ofHom j) hj C _ _ (𝟙 _) (𝟙 _) (fun _ _ h => h) (fun x => ⟨x, rfl⟩) hJ
  apply hdvd
  let i₀ : Fin C.length := (0 : Fin 2)
  have h0 : l = (S i₀).length * Δ.rank :=
    eq_length_mul_of_size_eq (S i₀) (refinement_size_eq S hS i₀)
  exact ⟨(S i₀).length, h0.trans (Nat.mul_comm _ _)⟩

end Segment

section Stages

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- The refinement of a block shape whose blocks have sizes `len j * r` into blocks of
size `r`. -/
def uniformRefinement {n r : ℕ} (hr : 0 < r) (C : BlockShape n) (len : Fin C.length → ℕ)
    (hlen : ∀ j, C.size j = len j * r) : BlockRefinement C := fun j =>
  { length := len j
    size := fun _ => r
    positive := fun _ => hr
    sum_eq := by rw [hlen j]; simp }

/-- Twisting by equal characters gives isomorphic representations. -/
def twistIsoOfEq {G : Type*} [Group G] [TopologicalSpace G] {χ η : G →* ℂˣ} (h : χ = η)
    (hχ : IsOpen (χ.ker : Set G)) (hη : IsOpen (η.ker : Set G))
    (A : SmoothRep.{0, _, uV} ℂ G) : A.twist χ hχ ≅ A.twist η hη := by
  subst h
  exact Iso.refl _

/-- `ν^s (ν^t A) ≅ ν^u A` whenever `u = s + t`. -/
def segmentFactorTwistIso {r : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (s t u : ℝ) (h : u = s + t) :
    letI := T.topology
    T.segmentFactor (T.segmentFactor A t) s ≅ T.segmentFactor A u := by
  let := T.topology
  subst h
  have hst : IsOpen ((T.determinantPowerCharacter r s * T.determinantPowerCharacter r t).ker :
      Set (GeneralLinear r F.Carrier)) := by
    rw [← realPowerCharacter_add]
    exact T.isOpen_ker_determinantPowerCharacter r (s + t)
  exact SmoothRep.twistTwistIso _ _ _ _ hst A ≪≫
    twistIsoOfEq (realPowerCharacter_add _ s t).symm _ _ A

/-- Normalized product induction from a shape equal to `uniform k r`: factors that are
pairwise isomorphic give isomorphic inductions. -/
theorem nonempty_productInduced_iso_uniform {k r : ℕ} (hr : 0 < r) (B : BlockShape (k * r))
    (hB : B = BlockShape.uniform k r hr)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (τ : letI := T.topology
      Fin k → SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hστ : letI := T.topology
      ∀ i j, i.val = j.val → ∀ x : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier),
        HEq x (σ i) → Nonempty (x ≅ τ j)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor B).obj σ ≅
      (T.normalizedProductInductionFunctor (BlockShape.uniform k r hr)).obj τ) := by
  let := T.topology
  subst hB
  exact ⟨(T.normalizedProductInductionFunctor _).mapIso
    (Pi.isoMk fun i => (hστ i i rfl (σ i) HEq.rfl).some)⟩

/-- **Induction in stages for a segment.** The segment induction of length `m` is the
normalized induction, from the split `(q r, (m - q) r)`, of the segment inductions of
the initial piece from `A` and of the terminal piece from `ν^q A`. -/
theorem nonempty_segmentInduced_iso_socleSplit (Δ : Segment.{uV, uF} T) (q : ℕ)
    (hq : 0 < q) (hqm : q < Δ.length)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear Δ.rank F.Carrier)) :
    letI := T.topology
    Nonempty (T.segmentInduced A Δ.length Δ.rank_pos ≅
      (T.normalizedProductInductionFunctor (Δ.socleSplitShape q hq hqm)).obj
        (Δ.socleSplitFactors q hq hqm (T.segmentInduced A q Δ.rank_pos)
          (T.segmentInduced (T.segmentFactor A (q : ℝ)) (Δ.length - q) Δ.rank_pos))) := by
  let := T.topology
  let r := Δ.rank
  have hr : 0 < r := Δ.rank_pos
  let C := Δ.socleSplitShape q hq hqm
  let len : Fin C.length → ℕ := ![q, Δ.length - q]
  have hlen : ∀ j, C.size j = len j * r := by
    intro j
    change Fin 2 at j
    fin_cases j <;> rfl
  let S : BlockRefinement C := uniformRefinement hr C len hlen
  let B := C.flatten S
  let e := C.flattenBlockEquiv S
  let h (a : (j : Fin C.length) × Fin (S j).length) : (S a.1).size a.2 = B.size (e a) :=
    (C.flatten_size_flattenBlockEquiv S a).symm
  let σ : ∀ k, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size k) F.Carrier) :=
    fun k => T.segmentFactor A ((k : ℕ) : ℝ)
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{uF, uV} F T Δ.degree B C S e h
    (fun j k x => C.index_index_eq_flatten S ⟨j, k⟩ x) σ
  have hB : B = BlockShape.uniform Δ.length r hr := eq_uniform_of_size_eq hr B (fun _ => rfl)
  obtain ⟨eflat⟩ := nonempty_productInduced_iso_uniform T hr B hB σ
    (T.segmentFactors A Δ.length hr)
    (fun i j hij x hx => ⟨eqToIso (eq_of_heq hx) ≪≫
      eqToIso (congrArg (fun t : ℕ => T.segmentFactor A (t : ℝ)) hij)⟩)
  let i₀ : Fin C.length := (0 : Fin 2)
  let i₁ : Fin C.length := (1 : Fin 2)
  have he₀ : ∀ k : Fin (S i₀).length, ((e ⟨i₀, k⟩ : Fin B.length) : ℕ) = k := by
    intro k
    refine (finSigmaFinEquiv_apply (n := fun j => (S j).length) ⟨i₀, k⟩).trans ?_
    exact (congrArg (· + (k : ℕ)) (Fin.sum_univ_zero _)).trans (Nat.zero_add _)
  have he₁ : ∀ k : Fin (S i₁).length, ((e ⟨i₁, k⟩ : Fin B.length) : ℕ) = q + k := by
    intro k
    refine (finSigmaFinEquiv_apply (n := fun j => (S j).length) ⟨i₁, k⟩).trans ?_
    exact congrArg (· + (k : ℕ)) (Fin.sum_univ_one _)
  refine ⟨eflat.symm ≪≫ ereg ≪≫ (T.normalizedProductInductionFunctor C).mapIso
    (Pi.isoMk (Fin.cons ?_ (Fin.cons ?_ finZeroElim)))⟩
  · refine (nonempty_productInduced_iso_uniform T (k := q) hr (S i₀) rfl _
      (T.segmentFactors A q hr) fun i j hij x hx => ?_).some
    have hx' : HEq x (σ (e ⟨i₀, i⟩)) := by
      refine hx.trans ?_
      simp only [eqRec_heq_iff, heq_eq_eq]
      rfl
    exact ⟨eqToIso (eq_of_heq hx') ≪≫
      eqToIso (congrArg (fun t : ℕ => T.segmentFactor A (t : ℝ)) ((he₀ i).trans hij))⟩
  · refine (nonempty_productInduced_iso_uniform T (k := Δ.length - q) hr (S i₁) rfl _
      (T.segmentFactors (T.segmentFactor A (q : ℝ)) (Δ.length - q) hr)
      fun i j hij x hx => ?_).some
    have hx' : HEq x (σ (e ⟨i₁, i⟩)) := by
      refine hx.trans ?_
      simp only [eqRec_heq_iff, heq_eq_eq]
      rfl
    exact ⟨eqToIso (eq_of_heq hx') ≪≫ (segmentFactorTwistIso T A ((j : ℕ) : ℝ) (q : ℝ)
      (((e ⟨i₁, i⟩ : Fin B.length) : ℕ) : ℝ) (by rw [he₁, hij]; push_cast; ring)).symm⟩

end Stages

section Embedding

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- The twist `ν^s A` of a supercuspidal representative `A`. -/
def twistRep {r : ℕ} (s : ℝ)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r) :=
  letI := T.topology
  SupercuspidalRep.twist (T.determinantPowerCharacter r s)
    (T.isOpen_ker_determinantPowerCharacter _ _)
    (T.ker_determinant_le_ker_determinantPowerCharacter _ _) A

/-- If `A` represents the beginning of `Δ`, then `ν^q A` represents the beginning of the
terminal subsegment from `q`. -/
theorem terminal_isRepresentedBy_twistRep (Δ : Segment.{uV, uF} T) (q : ℕ)
    (hqm : q < Δ.length)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A) :
    (Δ.terminal q hqm).base.IsRepresentedBy (twistRep T (q : ℝ) A) := by
  let := T.topology
  change T.supercuspidalClassRealPowerTwist Δ.rank (q : ℝ) A.isoClass =
    T.supercuspidalClassRealPowerTwist Δ.rank (q : ℝ) Δ.base.cls
  exact congrArg (T.supercuspidalClassRealPowerTwist _ _) hA

/-- The normalized induction, from the split `(q r, (m - q) r)`, of socles of the initial
and terminal subsegments embeds into the segment induction of `Δ`. -/
theorem exists_socleSplit_embedding (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (hA : Δ.base.IsRepresentedBy A)
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.initial q hq).degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.terminal q hqm).degree F.Carrier))
    (h₁ : T.IsSegmentSocle (Δ.initial q hq) π₁)
    (h₂ : T.IsSegmentSocle (Δ.terminal q hqm) π₂) :
    letI := T.topology
    ∃ J : ((T.normalizedProductInductionFunctor (Δ.socleSplitShape q hq hqm)).obj
        (Δ.socleSplitFactors q hq hqm π₁ π₂)).representation.IntertwiningMap
        (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation,
      Function.Injective J := by
  let := T.topology
  obtain ⟨-, j₁, hj₁, -⟩ := (T.isSegmentSocle_iff (Δ.initial q hq) π₁ A hA).mp h₁
  obtain ⟨-, j₂, hj₂, -⟩ := (T.isSegmentSocle_iff (Δ.terminal q hqm) π₂
    (twistRep T (q : ℝ) A) (terminal_isRepresentedBy_twistRep T Δ q hqm A hA)).mp h₂
  obtain ⟨J, hJ⟩ := Classification.normalizedProduct_embedding_of_factor_embeddings F T
    (Δ.socleSplitShape q hq hqm) (Δ.socleSplitFactors q hq hqm π₁ π₂)
    (Δ.socleSplitFactors q hq hqm (T.segmentInduced A.obj q Δ.rank_pos)
      (T.segmentInduced (T.segmentFactor A.obj (q : ℝ)) (Δ.length - q) Δ.rank_pos))
    (Fin.cons j₁ (Fin.cons j₂ finZeroElim)) (Fin.cons hj₁ (Fin.cons hj₂ finZeroElim))
  obtain ⟨e⟩ := nonempty_segmentInduced_iso_socleSplit T Δ q hq hqm A.obj
  exact ⟨(SmoothRep.equivOfIso e.symm).toIntertwiningMap.comp J,
    (SmoothRep.equivOfIso e.symm).injective.comp hJ⟩

end Embedding

section Injectivity

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- **Injectivity of Jacquet quotient maps.** Let `π` embed in the normalized induction of
a quasicuspidal `ρ` from the uniform shape `(r, …, r)`, and let the normalized Jacquet
module of `π` along that shape be irreducible. Then every surjection from a normalized
Jacquet module `r_C(π)` onto a nonzero representation is injective. -/
theorem jacquet_map_injective {m r : ℕ} (hr : 0 < r)
    (hH2 : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T (m * r)) :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ ((BlockShape.uniform m r hr).Levi F.Carrier)),
      IsLeviQuasicuspidal (BlockShape.uniform m r hr) ρ.representation →
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier))
      (j : π ⟶ (T.normalizedParabolicInductionFunctor (BlockShape.uniform m r hr)).obj ρ),
      Function.Injective (SmoothRep.hom j) →
      (∀ B : BlockShape (m * r), B = BlockShape.uniform m r hr →
        ((T.normalizedJacquetFunctor B).obj π).IsIrreducible) →
    ∀ (C : BlockShape (m * r)) (X : SmoothRep.{0, uF, max uF uV} ℂ (C.Levi F.Carrier))
      (φ : (T.normalizedJacquetFunctor C).obj π ⟶ X),
      Function.Surjective (SmoothRep.hom φ) → Nontrivial X →
      Function.Injective (SmoothRep.hom φ) := by
  let := T.topology
  intro ρ hρ π j hj hirr C X φ hφ hX
  refine (injective_iff_map_eq_zero (SmoothRep.hom φ)).mpr fun x hx => ?_
  by_contra hx0
  let K := (SmoothRep.hom φ).ker
  let ι := SmoothRep.subtype ((T.normalizedJacquetFunctor C).obj π) K
  have hY : Nontrivial (SmoothRep.subrepresentation ((T.normalizedJacquetFunctor C).obj π) K) :=
    ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨S, hS, hneY⟩ := exists_refinement_size_eq T hr hH2 ρ hρ π j hj C _ _ ι (𝟙 _)
    (SmoothRep.subtype_injective _ K) (fun y => ⟨y, rfl⟩) hY
  obtain ⟨S', hS', hneX⟩ := exists_refinement_size_eq T hr hH2 ρ hρ π j hj C _ X (𝟙 _) φ
    (fun _ _ h => h) hφ hX
  have hSS' : S = S' := refinement_eq_of_size_eq hr S S' hS hS'
  rw [← hSS'] at hneX
  have hB : C.flatten S = BlockShape.uniform m r hr := eq_uniform_of_size_eq hr _ hS
  have : Representation.IsIrreducible
      ((T.normalizedJacquetFunctor (C.flatten S)).obj π).representation := hirr _ hB
  let g := flattenedQuotient T C S π ≫ flattenedRefinedJacquetMap T C S φ
  have hg : Function.Surjective (SmoothRep.hom g) := by
    rw [SmoothRep.hom_comp]
    exact (flattenedRefinedJacquetMap_surjective T C S φ hφ).comp
      (flattenedQuotient_surjective T C S π)
  have hg0 : SmoothRep.hom g ≠ 0 := by
    intro h
    have : Nontrivial (flattenedRefinedJacquet T C S X) := hneX
    obtain ⟨t, ht⟩ := exists_ne (0 : flattenedRefinedJacquet T C S X)
    obtain ⟨w, hw⟩ := hg t
    exact ht (hw.symm.trans (DFunLike.congr_fun h w))
  have hginj : Function.Injective (SmoothRep.hom g) :=
    (Representation.IsIrreducible.injective_or_eq_zero (SmoothRep.hom g)).resolve_right hg0
  obtain ⟨y, hy⟩ := exists_ne (0 : RefinedJacquetModule C S
    (SmoothRep.subrepresentation ((T.normalizedJacquetFunctor C).obj π) K).representation)
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ (refinedUnipotent F.Carrier C S) y
  let z := SmoothRep.hom (flattenedRefinedJacquetMap T C S ι)
    (refinedJacquetMk C S
      (SmoothRep.subrepresentation ((T.normalizedJacquetFunctor C).obj π) K).representation v)
  have hz : z ≠ 0 := fun h => hy (flattenedRefinedJacquetMap_injective T C S ι
    (SmoothRep.subtype_injective _ K) (h.trans (map_zero _).symm))
  have hφz : SmoothRep.hom (flattenedRefinedJacquetMap T C S φ) z = 0 := by
    have hv : SmoothRep.hom φ (SmoothRep.hom ι v) = 0 := Subtype.property v
    change refinedJacquetMk C S X.representation (SmoothRep.hom φ (SmoothRep.hom ι v)) = 0
    rw [hv, map_zero]
  obtain ⟨w, hw⟩ := flattenedQuotient_surjective T C S π z
  have hgw : SmoothRep.hom g w = SmoothRep.hom g 0 := by
    rw [map_zero]
    change SmoothRep.hom (flattenedRefinedJacquetMap T C S φ)
      (SmoothRep.hom (flattenedQuotient T C S π) w) = 0
    rw [hw]
    exact hφz
  have hw0 : w = 0 := hginj hgw
  exact hz (hw.symm.trans (by rw [hw0, map_zero]))

end Injectivity

section SocleFactors

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- An irreducible representation has a nontrivial carrier. -/
theorem nontrivial_of_isIrreducible {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  have := h
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule

/-- A segment socle is irreducible and admissible. -/
theorem isIrreducible_isAdmissible_of_isSegmentSocle (Δ : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (h : T.IsSegmentSocle Δ π) :
    letI := T.topology
    π.IsIrreducible ∧ IsAdmissible π.representation := by
  let := T.topology
  obtain ⟨A, -, hirr, j, hj, -⟩ := h
  exact ⟨hirr, isAdmissible_of_injective j hj
    (Classification.segmentInductionAdmissibility F T Δ.length Δ.rank_pos A.obj
      A.property.2.1).2.2.1⟩

/-- The external tensor product of socles of the initial and terminal subsegments is
irreducible. -/
theorem isIrreducible_socleSplitTensor (Δ : Segment.{uV, uF} T) (q : ℕ) (hq : 0 < q)
    (hqm : q < Δ.length)
    (π₁ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.initial q hq).degree F.Carrier))
    (π₂ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.terminal q hqm).degree F.Carrier))
    (h₁ : T.IsSegmentSocle (Δ.initial q hq) π₁)
    (h₂ : T.IsSegmentSocle (Δ.terminal q hqm) π₂) :
    letI := T.topology
    (FiniteTensor.externalFunctor.obj (Δ.socleSplitFactors q hq hqm π₁ π₂)).IsIrreducible := by
  let := T.topology
  obtain ⟨hi₁, ha₁⟩ := isIrreducible_isAdmissible_of_isSegmentSocle T _ π₁ h₁
  obtain ⟨hi₂, ha₂⟩ := isIrreducible_isAdmissible_of_isSegmentSocle T _ π₂ h₂
  let := T.generalLinearTopologicalGroup (Δ.initial q hq).degree
  let := T.generalLinearTopologicalGroup (Δ.terminal q hqm).degree
  have hirr : ∀ i, ((Δ.socleSplitFactors q hq hqm π₁ π₂) i).representation.IsIrreducible :=
    Fin.cons hi₁ (Fin.cons hi₂ finZeroElim)
  have hS : ∀ i, ∀ φ : ((Δ.socleSplitFactors q hq hqm π₁ π₂) i).representation.IntertwiningMap
      ((Δ.socleSplitFactors q hq hqm π₁ π₂) i).representation,
      ∃ c : ℂ, φ = c • Representation.IntertwiningMap.id _ :=
    Fin.cons (fun φ => ((admissibleSchur (W := ℂ) π₁.representation ha₁ hi₁).1 φ).exists)
      (Fin.cons (fun φ => ((admissibleSchur (W := ℂ) π₂.representation ha₂ hi₂).1 φ).exists)
        finZeroElim)
  exact FiniteTensor.isIrreducible_external _ hS

/-- **Finite length.** The segment induction has finite length. -/
theorem segmentInduced_finiteLength
    (hH4 : ∀ n, CuspidalInductionLengthTheorem.{uF, uV} F T n) (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)) :
    letI := T.topology
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear Δ.degree F.Carrier))
      (T.segmentInduced A.obj Δ.length Δ.rank_pos).representation.asModule := by
  let := T.topology
  have hc := Classification.segmentFactors_isIrreducible_isLeviCuspidal F T Δ.length
    Δ.length_pos Δ.rank_pos A
  exact (hH4 _ (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos)
    (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj Δ.length Δ.rank_pos))
    hc.1 hc.2).1

/-- By Zelevinsky 1980, 3.1, the normalized Jacquet module of a segment
subrepresentation along the uniform shape is irreducible. -/
theorem isIrreducible_jacquet_uniform
    (hH1 : Classification.SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    (Δ : Segment.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hA : Δ.base.IsRepresentedBy A) (hπ : T.IsSegmentSubrepresentation Δ π) :
    letI := T.topology
    ∀ B : BlockShape (Δ.length * Δ.rank), B = BlockShape.uniform Δ.length Δ.rank Δ.rank_pos →
      ((T.normalizedJacquetFunctor B).obj π).IsIrreducible := by
  let := T.topology
  intro B hB
  subst hB
  obtain ⟨e⟩ := hH1 Δ A π hA hπ
  exact (isIrreducible_iff_of_equiv e).mpr
    (Classification.segmentFactors_isIrreducible_isLeviCuspidal F T Δ.length Δ.length_pos
      Δ.rank_pos A).1

end SocleFactors

section Assembly

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

open PadicField.TopologicalData

/-- **Clause 2 of Ze80 3.4.** The normalized Jacquet module of a segment socle along
`(q r, (m - q) r)` is isomorphic to the external tensor product of socles of the initial
and terminal subsegments. -/
theorem nonempty_socleSplit_jacquet_iso
    (hH1 : Classification.SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    (hH2 : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hH4 : ∀ n, CuspidalInductionLengthTheorem.{uF, uV} F T n) :
    letI := T.topology
    ∀ (Δ : Segment.{uV, uF} T)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π →
    ∀ (q : ℕ) (hq : 0 < q) (hqm : q < Δ.length)
      (π₁ : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (Δ.initial q hq).degree F.Carrier))
      (π₂ : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (Δ.terminal q hqm).degree F.Carrier)),
      T.IsSegmentSocle (Δ.initial q hq) π₁ → T.IsSegmentSocle (Δ.terminal q hqm) π₂ →
      Nonempty ((T.normalizedJacquetFunctor (Δ.socleSplitShape q hq hqm)).obj π ≅
        FiniteTensor.externalFunctor.obj (Δ.socleSplitFactors q hq hqm π₁ π₂)) := by
  let := T.topology
  intro Δ π hπ q hq hqm π₁ π₂ h₁ h₂
  have hπsub := hπ.isSegmentSubrepresentation
  obtain ⟨A, hA, hs⟩ := hπ
  obtain ⟨hi₁, -⟩ := isIrreducible_isAdmissible_of_isSegmentSocle T _ π₁ h₁
  obtain ⟨hi₂, -⟩ := isIrreducible_isAdmissible_of_isSegmentSocle T _ π₂ h₂
  have hW := RegularHeadExistence.nontrivial_normalizedProductInduction T
    (Δ.socleSplitShape q hq hqm) (Δ.socleSplitFactors q hq hqm π₁ π₂)
    (Fin.cons (nontrivial_of_isIrreducible π₁.representation hi₁)
      (Fin.cons (nontrivial_of_isIrreducible π₂.representation hi₂) finZeroElim))
  obtain ⟨J, hJ⟩ := exists_socleSplit_embedding T Δ q hq hqm A hA π₁ π₂ h₁ h₂
  obtain ⟨jπ, hjπ, hmem⟩ := exists_mem_range_of_isIrreducibleSocle hs
    (segmentInduced_finiteLength T hH4 Δ A) hW J hJ
  obtain ⟨ψ, hψ⟩ := exists_lift_of_mem_range J hJ jπ hmem
  have hψ0 : ψ ≠ 0 := by
    intro h0
    have := nontrivial_of_isIrreducible π.representation hs.1
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    have hjx : jπ x = 0 := by
      rw [← hψ, h0]
      exact map_zero J
    exact hx (hjπ (hjx.trans (map_zero jπ).symm))
  have hτ := isIrreducible_socleSplitTensor T Δ q hq hqm π₁ π₂ h₁ h₂
  let E := Parabolic.FirstAdjointness.equiv T (Δ.socleSplitShape q hq hqm)
    (σ := (FiniteTensor.externalFunctor.obj (Δ.socleSplitFactors q hq hqm π₁ π₂)).representation)
    π.isSmooth
  let φ : (T.normalizedJacquetFunctor (Δ.socleSplitShape q hq hqm)).obj π ⟶
      FiniteTensor.externalFunctor.obj (Δ.socleSplitFactors q hq hqm π₁ π₂) :=
    SmoothRep.ofHom (E ψ)
  have hφ0 : SmoothRep.hom φ ≠ 0 := fun h => hψ0 (E.map_eq_zero_iff.mp h)
  have hφs : Function.Surjective (SmoothRep.hom φ) := by
    have := hτ
    exact (Representation.IsIrreducible.surjective_or_eq_zero (SmoothRep.hom φ)).resolve_right
      hφ0
  have hφi : Function.Injective (SmoothRep.hom φ) :=
    jacquet_map_injective T Δ.rank_pos (hH2 _)
      (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj Δ.length Δ.rank_pos))
      (segmentFactors_isLeviQuasicuspidal T Δ.length Δ.length_pos Δ.rank_pos A)
      π (SmoothRep.ofHom jπ) hjπ (isIrreducible_jacquet_uniform T hH1 Δ A π hA hπsub)
      (Δ.socleSplitShape q hq hqm) _ φ hφs (nontrivial_of_isIrreducible _ hτ)
  exact ⟨SmoothRep.mkIso ((SmoothRep.hom φ).ofBijective ⟨hφi, hφs⟩)⟩

/-- **Zelevinsky 1980, Proposition 3.4**, conditional on Ze80 3.1 for segment
subrepresentations, BZ77 2.13(b), the existence of segment socles (Ze80 3.1) and finite
length of irreducible cuspidal induction. -/
theorem segmentSocleJacquetFormula_of
    (hH1 : Classification.SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    (hH2 : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hH3 : Classification.SegmentZelevinskyConstituentExistence.{uF, uV} F T)
    (hH4 : ∀ n, CuspidalInductionLengthTheorem.{uF, uV} F T n) :
    Classification.SegmentSocleJacquetFormula.{uF, uV} F T := by
  let := T.topology
  intro Δ π hπ
  refine ⟨jacquet_ofPair_subsingleton T hH2 Δ π hπ.isSegmentSubrepresentation,
    fun q hq hqm => ?_⟩
  obtain ⟨π₁, h₁, -⟩ := hH3 (Δ.initial q hq)
  obtain ⟨π₂, h₂, -⟩ := hH3 (Δ.terminal q hqm)
  exact ⟨π₁, π₂, h₁, h₂,
    nonempty_socleSplit_jacquet_iso T hH1 hH2 hH4 Δ π hπ q hq hqm π₁ π₂ h₁ h₂⟩

end Assembly

end Langlands.Classification.SegmentSocleJacquetReduction
