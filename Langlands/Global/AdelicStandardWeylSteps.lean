import Langlands.Global.AdelicStandardRootFunctional
import Langlands.Global.AdelicIntertwiningParameterShift
import Langlands.Global.AdelicWeylTorusAlignment
import Langlands.Global.AdelicWeylFamilyCounting
import Langlands.GroupScheme.Rational.StandardWeylElementaryChainProof
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison
import Langlands.Group.RelativeWeylRankOneChain

/-! # Weyl conjugations between the standard parabolics of a family

For a standard parabolic family `fam`:

* a Weyl conjugation `(w, c)` from `P_I` to `P_I'` has a representative `w z`, with `z` a
  rational point of `M_I`, normalizing the maximal split torus;
* a normalizer point `n` whose action carries the simple roots of `K` onto those of `K'` presents
  a Weyl conjugation from `P_K` to `P_K'`;
* a normalizer point presenting a Weyl conjugation from `P_K` to `P_K'` conjugates the standard
  relative Weyl subgroups `W_K` onto `W_K'`;
* the intertwining operator of a step `n ∈ M_S(F)`, `S = K ∪ {a}`, is invariant under translation
  of its parameter by the kernel of the root form of `a`;
* two Weyl conjugations whose points differ by a rational point of the source Levi have the same
  intertwining operator on left `U(𝔸)M(F)`-invariant functions, for any retractions.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom]
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}

/-- In a Coxeter realization, the root action of any lift of a Weyl element raising the length on
the simple reflections of `L`, and conjugating them bijectively onto those of `L'`, carries the
simple roots of `L` onto those of `L'`. -/
theorem weylAction_image_rootSet_of_simple_bijection {CM : CoxeterMatrix (SimpleRoot i ν)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)} (h : IsRelativeWeylCoxeterRealization i ν cs)
    {L L' : Finset (SimpleRoot i ν)} {g : relativeWeylGroup i}
    (hpos : ∀ a ∈ L, cs.length g < cs.length (g * cs.simple a))
    (hinto : ∀ a ∈ L, ∃ b ∈ L', g * cs.simple a * g⁻¹ = cs.simple b)
    (honto : ∀ b ∈ L', ∃ a ∈ L, g * cs.simple a * g⁻¹ = cs.simple b)
    (n : normalizerPoints i) (hn : (QuotientGroup.mk n : relativeWeylGroup i) = g) :
    weylAction i n '' rootSet i ν L = rootSet i ν L' := by
  subst hn
  rw [← schemeWeylCharacterAction_mk]
  ext α
  constructor
  · rintro ⟨β, ⟨a, ha, rfl⟩, rfl⟩
    have ha' : a ∈ L := ha
    obtain ⟨b, hb, he⟩ := hinto a ha'
    exact ⟨b, hb, (h.root_eq_of_conj_simple _ a b ((h.2.2.1 _ a).mp (hpos a ha')) he).symm⟩
  · rintro ⟨b, hb, rfl⟩
    have hb' : b ∈ L' := hb
    obtain ⟨a, ha, he⟩ := honto b hb'
    exact ⟨a.val, ⟨a, ha, rfl⟩,
      h.root_eq_of_conj_simple _ a b ((h.2.2.1 _ a).mp (hpos a ha)) he⟩

omit [Mono i.hom.hom.left] in
theorem rootSet_insert [DecidableEq (SimpleRoot i ν)] (a : SimpleRoot i ν)
    (L : Finset (SimpleRoot i ν)) :
    rootSet i ν (insert a L) = insert a.val (rootSet i ν L) := by
  rw [rootSet, Finset.coe_insert, Set.image_insert_eq]
  rfl

end Langlands.GroupScheme

namespace Langlands.Global

open Langlands.GroupScheme

/-- The range of a subgroup map followed by an ambient isomorphism is the preimage of the
original range under the inverse isomorphism. -/
theorem range_comp_iso_hom_eq_comap_inv {S : Scheme.{u}} {H G : GroupScheme S}
    (j : H ⟶ G) (e : G ≅ G) :
    SubgroupFunctor.range (j ≫ e.hom) = (SubgroupFunctor.range j).comap e.inv := by
  ext T x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom e.hom e.inv,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom e.inv e.hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

namespace AdelicGroupPoints

variable {F : Type u} [Field F]

/-- The transported parameter does not depend on the retraction of the target Levi. -/
theorem weylParameter_retraction_eq {P M Q M' : GroupScheme (Spec (CommRingCat.of F))}
    (l : M ⟶ P) (c : M' ⟶ M) {l' : M' ⟶ Q} (hl' : IsRationalLeviSubgroup l')
    {π₁ π₂ : Q ⟶ M'} (h₁ : l' ≫ π₁ = 𝟙 M') (h₂ : l' ≫ π₂ = 𝟙 M') :
    weylParameter (F := F) l c π₁ = weylParameter l c π₂ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s χ
  simp only [weylParameter_tmul]
  congr 1
  apply hl'.characterRestrict_bijective.1
  simp only [← AddMonoidHom.comp_apply, ← characterRestrict_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂]

end AdelicGroupPoints

namespace StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Point" => (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

omit [NumberField F] in
theorem mono_levi_comp (J : StandardIndex F G fam.i fam.ν) :
    Mono (fam.l J ≫ fam.p J).hom.hom.left :=
  ((fam.isCompatible J).levi.isClosedSubgroup.comp
    (fam.isCompatible J).parabolic.isClosedSubgroup).mono

omit [NumberField F] in
theorem mono_levi_comp_grp (J : StandardIndex F G fam.i fam.ν) :
    Mono (fam.l J ≫ fam.p J) := by
  have := fam.mono_levi_comp J
  have hp : Mono (fam.l J ≫ fam.p J).hom.hom := Over.mono_of_mono_left _
  exact (Grp.forget _).mono_of_mono_map (f := fam.l J ≫ fam.p J) hp

omit [NumberField F] in
theorem mono_p_left (J : StandardIndex F G fam.i fam.ν) : Mono (fam.p J).hom.hom.left :=
  (fam.isCompatible J).parabolic.isClosedSubgroup.mono

omit [NumberField F] in
/-- The rational points of the standard Levi of `J` are those of the image of `M_J`. -/
theorem mem_standardLeviPoints_iff (J : StandardIndex F G fam.i fam.ν) (x : Point) :
    x ∈ standardLeviPoints fam.i fam.ν J.val ↔
      ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (fam.M J).X,
        z ≫ (fam.l J ≫ fam.p J).hom.hom = x := by
  change x ∈ (standardLevi fam.i fam.ν J.val).carrier _ ↔ _
  rw [← (fam.isCompatible J).levi_eq]
  exact SubgroupFunctor.mem_range

omit [NumberField F] in
/-- Every standard index is the root set of a finite set of simple roots. -/
theorem exists_rootSet_eq [Finite (SimpleRoot fam.i fam.ν)] (J : StandardIndex F G fam.i fam.ν) :
    ∃ L : Finset (SimpleRoot fam.i fam.ν), rootSet fam.i fam.ν L = J.val := by
  classical
  have := Fintype.ofFinite (SimpleRoot fam.i fam.ν)
  refine ⟨Finset.univ.filter (fun a => a.val ∈ J.val), ?_⟩
  ext α
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.mp ha).2
  · intro hα
    exact ⟨⟨α, J.property hα⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩, rfl⟩

/-- **Normalizing representative.** A Weyl conjugation `(w, c)` from `P_I` to `P_I'` has a
representative `w z`, with `z` a rational point of `M_I`, normalizing the maximal split torus. -/
theorem exists_normalizerPoints_mul_levi {I I' : StandardIndex F G fam.i fam.ν}
    {w : Point} {c : fam.M I' ⟶ fam.M I}
    (hw : IsWeylConjugation (fam.p I) (fam.l I) (fam.p I') (fam.l I') w c) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (fam.M I).X,
      w * (z ≫ (fam.l I ≫ fam.p I).hom.hom) ∈ normalizerPoints fam.i := by
  obtain ⟨z, e, he⟩ := weylTorusAlignment F G (fam.P I) (fam.M I) (fam.P I') (fam.M I')
    (fam.A I) (fam.A I') (fam.p I) (fam.l I) (fam.a I) (fam.rootPresentation I)
    (fam.p I') (fam.l I') (fam.a I') (fam.rootPresentation I') w c hw
  refine ⟨z, ?_⟩
  have h : IsNormalizingPoint fam.i (w * (z ≫ (fam.l I ≫ fam.p I).hom.hom))⁻¹
      (CommGroupScheme.isoOfGroupIso e) := by
    rw [IsNormalizingPoint, innerIso_inv_hom]
    exact he
  simpa using (normalizerPoints fam.i).inv_mem ⟨_, h⟩

omit [NumberField F] in
/-- The standard Levis of a Weyl conjugation between standard parabolics are conjugate:
`x ∈ M_K(F)` exactly when `n x n⁻¹ ∈ M_K'(F)`. -/
theorem mem_standardLeviPoints_iff_of_isWeylConjugation {K K' : StandardIndex F G fam.i fam.ν}
    {n : Point} {c : fam.M K' ⟶ fam.M K}
    (hc : IsWeylConjugation (fam.p K) (fam.l K) (fam.p K') (fam.l K') n c) (x : Point) :
    x ∈ standardLeviPoints fam.i fam.ν K.val ↔
      n * x * n⁻¹ ∈ standardLeviPoints fam.i fam.ν K'.val := by
  have := hc.isIso
  have hrange : SubgroupFunctor.range (fam.l K ≫ fam.p K) =
      (SubgroupFunctor.range (fam.l K' ≫ fam.p K')).comap (G.innerIso n).hom := by
    have h1 : SubgroupFunctor.range (c ≫ fam.l K ≫ fam.p K) =
        SubgroupFunctor.range (fam.l K ≫ fam.p K) := by
      ext T y
      rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
      constructor
      · rintro ⟨y', rfl⟩
        exact ⟨y' ≫ c.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩
      · rintro ⟨y', rfl⟩
        refine ⟨y' ≫ (inv c).hom.hom, ?_⟩
        simp only [Grp.comp_hom_hom, Category.assoc]
        rw [← Category.assoc (inv c).hom.hom, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
          Grp.id_hom_hom, Category.id_comp]
    rw [← h1, hc.comp_eq, ← Category.assoc]
    exact range_comp_iso_hom_eq_comap_inv _ (G.innerIso n).symm
  change x ∈ (standardLevi fam.i fam.ν K.val).carrier _ ↔
    n * x * n⁻¹ ∈ (standardLevi fam.i fam.ν K'.val).carrier _
  rw [← (fam.isCompatible K).levi_eq, ← (fam.isCompatible K').levi_eq, hrange,
    SubgroupFunctor.mem_comap, comp_innerIso_hom, constantPoint_self]

omit [NumberField F] in
/-- A normalizer point presenting a Weyl conjugation from `P_K` to `P_K'` conjugates the standard
relative Weyl subgroups `W_K` onto `W_K'`. -/
theorem mem_standardRelativeWeylGroup_iff_of_isWeylConjugation
    {K K' : StandardIndex F G fam.i fam.ν} {n : normalizerPoints fam.i}
    {c : fam.M K' ⟶ fam.M K}
    (hc : IsWeylConjugation (fam.p K) (fam.l K) (fam.p K') (fam.l K') n.val c)
    (g : relativeWeylGroup fam.i) :
    g ∈ standardRelativeWeylGroup fam.i fam.ν K'.val ↔
      (QuotientGroup.mk n : relativeWeylGroup fam.i)⁻¹ * g * QuotientGroup.mk n ∈
        standardRelativeWeylGroup fam.i fam.ν K.val := by
  have hiff := fam.mem_standardLeviPoints_iff_of_isWeylConjugation hc
  rw [mem_standardRelativeWeylGroup_iff, mem_standardRelativeWeylGroup_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨n⁻¹ * m * n, ?_, by simp⟩
    rw [hiff]
    have he : n.val * (n⁻¹ * m * n : normalizerPoints fam.i).val * n.val⁻¹ = m.val := by
      push_cast
      group
    rw [he]
    exact hm
  · rintro ⟨m, hm, hme⟩
    refine ⟨n * m * n⁻¹, ?_, ?_⟩
    · have h := (hiff m.val).mp hm
      push_cast
      exact h
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hme]
      group

omit [NumberField F] in
/-- **Weyl conjugations from the root action.** A normalizer point whose action carries the simple
roots of `K` onto those of `K'` presents a Weyl conjugation from `P_K` to `P_K'`. -/
theorem exists_isWeylConjugation_of_image {K K' : StandardIndex F G fam.i fam.ν}
    (n : normalizerPoints fam.i) (h : weylAction fam.i n '' K.val = K'.val) :
    ∃ c : fam.M K' ⟶ fam.M K,
      IsWeylConjugation (fam.p K) (fam.l K) (fam.p K') (fam.l K') n.val c := by
  have := fam.mono_levi_comp K
  have := fam.mono_levi_comp K'
  have hrange : SubgroupFunctor.range ((fam.l K' ≫ fam.p K') ≫ (G.innerIso n.val).inv) =
      SubgroupFunctor.range (fam.l K ≫ fam.p K) := by
    have hK : K.val ⊆ relativeRoots fam.i := K.property.trans
      ((simpleRelativeRoots_subset_positive fam.i fam.ν).trans
        (positiveRelativeRoots_subset_relativeRoots fam.i fam.ν))
    have hconj := (standardLeviConjugation F G fam.connectedReductive fam.T fam.i
      fam.maximalSplit fam.ν fam.generic).1 K'.val K.val K'.property K.property n
      (relativeRootSubset_image_of_character_image fam.i hK n h)
    rw [(fam.isCompatible K).levi_eq, hconj, ← (fam.isCompatible K').levi_eq]
    exact range_comp_iso_hom_eq_comap_inv _ (G.innerIso n.val).symm
  refine ⟨SubgroupFunctor.rangeFactor _ (fam.l K ≫ fam.p K) hrange.le, ⟨?_, ?_⟩⟩
  · have : Mono (fam.l K ≫ fam.p K).hom.hom := Over.mono_of_mono_left _
    have : Mono ((fam.l K' ≫ fam.p K') ≫ (G.innerIso n.val).inv).hom.hom := by
      have : Mono (fam.l K' ≫ fam.p K').hom.hom := Over.mono_of_mono_left _
      rw [Grp.comp_hom_hom]
      infer_instance
    exact SubgroupFunctor.isIso_factor_of_range_eq _ _ _
      (SubgroupFunctor.rangeFactor_comp _ _ hrange.le) hrange
  · rw [SubgroupFunctor.rangeFactor_comp]
    simp only [Category.assoc]

/-- The intertwining operator of a family step `n ∈ M_S(F)`, with `S = L ∪ {a}` for a simple
root `a ∉ L` and `L' ⊆ S`, does not change when its parameter is translated by an element of the
kernel of the root form of `a ∘ f_L`. -/
theorem intertwiningOperator_add_of_rootFunctional_eq_zero
    [∀ J, IsClosedImmersion (fam.p J).hom.hom.left]
    [∀ J, Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]
    [Fintype (relativeWeylGroup fam.i)]
    {K : Subgroup (AdelicGroupPoints F G)} (hK : ∀ J, IsIwasawaCompact (fam.p J) K)
    {L L' S : StandardIndex F G fam.i fam.ν} {a : characterLattice fam.T}
    (ha : a ∈ simpleRelativeRoots fam.i fam.ν) (hS : S.val = insert a L.val)
    (hL'S : L'.val ⊆ S.val) {n : Point} (hn : n ∈ standardLeviPoints fam.i fam.ν S.val)
    {c : fam.M L' ⟶ fam.M L}
    (hc : IsWeylConjugation (fam.p L) (fam.l L) (fam.p L') (fam.l L') n c)
    {π' : fam.P L' ⟶ fam.M L'} (hπ' : fam.l L' ≫ π' = 𝟙 _) (ψ : AdelicGroupPoints F G → ℂ)
    (mu nu : ComplexCharacterParameter F (fam.P L))
    (hnu : (fam.rootPresentation L).rootFunctional
      (fam.isCompatible L).splitComponent.isCentralSplitTorus.1.1
      fam.maximalSplit.isSplitSubtorus.1 (fam.f L ≫ a) nu = 0)
    (g : AdelicGroupPoints F G) :
    (hK L).intertwiningOperator (hK L') (fam.iU L) (fam.l L) (fam.iU L') c π' n ψ (mu + nu) g =
      (hK L).intertwiningOperator (hK L') (fam.iU L) (fam.l L) (fam.iU L') c π' n ψ mu g := by
  have := fam.mono_p_left S
  have hLS : L ≤ S := by
    change L.val ⊆ S.val
    rw [hS]
    exact Set.subset_insert _ _
  have hle := (fam.le_iff_range_le L S).mp hLS
  have hle' := (fam.le_iff_range_le L' S).mp hL'S
  obtain ⟨νS, hνS⟩ := fam.exists_parameterRestrict_of_rootFunctional_eq_zero ha hS
    (SubgroupFunctor.rangeFactor (fam.p L) (fam.p S) hle)
    (SubgroupFunctor.rangeFactor_comp _ _ hle) hnu
  obtain ⟨z, hz⟩ := (fam.mem_standardLeviPoints_iff S n).mp hn
  rw [← hνS]
  exact (hK L).intertwiningOperator_add_parameterRestrict (hK L') (hK S)
    (SubgroupFunctor.rangeFactor (fam.p L) (fam.p S) hle) (SubgroupFunctor.rangeFactor_comp _ _ hle)
    (SubgroupFunctor.rangeFactor (fam.p L') (fam.p S) hle')
    (SubgroupFunctor.rangeFactor_comp _ _ hle') (fam.isCompatible L').levi hπ' hc
    (z ≫ (fam.l S).hom.hom) (by rw [← hz, Grp.comp_hom_hom, Category.assoc])
    (fam.isUnipotentRadical L').1.isUnipotent ψ mu νS g

/-- **Change of representative.** Two Weyl conjugations from `P_I` to `P_K` whose points differ on
the right by a rational point of `M_I` have the same intertwining operator on left
`U_I(𝔸)M_I(F)`-invariant functions, for any retractions of the target Levi. -/
theorem intertwiningOperator_eq_of_eq_mul_levi [∀ J, IsClosedImmersion (fam.p J).hom.hom.left]
    {K : Subgroup (AdelicGroupPoints F G)} (hK : ∀ J, IsIwasawaCompact (fam.p J) K)
    {I Q Q' : StandardIndex F G fam.i fam.ν} (hQ : Q = Q') {w w' : Point}
    {c : fam.M Q ⟶ fam.M I} {c' : fam.M Q' ⟶ fam.M I}
    {π : fam.P Q ⟶ fam.M Q} {π' : fam.P Q' ⟶ fam.M Q'}
    (hw : IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q) (fam.l Q) w c)
    (hw' : IsWeylConjugation (fam.p I) (fam.l I) (fam.p Q') (fam.l Q') w' c')
    (hπ : fam.l Q ≫ π = 𝟙 _) (hπ' : fam.l Q' ≫ π' = 𝟙 _)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (fam.M I).X)
    (hz : w' = w * (z ≫ (fam.l I ≫ fam.p I).hom.hom)) (ψ : AdelicGroupPoints F G → ℂ)
    (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p I) (fam.iU I) (fam.l I)) ψ)
    (mu : ComplexCharacterParameter F (fam.P I)) (g : AdelicGroupPoints F G) :
    (hK I).intertwiningOperator (hK Q) (fam.iU I) (fam.l I) (fam.iU Q) c π w ψ mu g =
      (hK I).intertwiningOperator (hK Q') (fam.iU I) (fam.l I) (fam.iU Q') c' π' w' ψ mu g := by
  subst hQ
  have hmono := fam.mono_levi_comp_grp I
  have hc' : c' = c ≫ ((fam.M I).innerIso z).inv := by
    rw [← cancel_mono (fam.l I ≫ fam.p I), hw'.comp_eq, hz, (hw.mul_right_levi z).comp_eq]
  obtain ⟨-, hpar, hop⟩ := intertwiningRightLeviRepresentative F G (fam.P I) (fam.M I) (fam.U I)
    (fam.P Q) (fam.M Q) (fam.U Q) (fam.p I) (fam.iU I) (fam.l I) (fam.p Q) (fam.iU Q) (fam.l Q)
    π' w c z hw (fam.isCompatible I).levi (fam.isUnipotentRadical I) K (hK I) (hK Q) ψ hψ
  rw [hc', hz, hop mu g]
  unfold IsIwasawaCompact.intertwiningOperator
  rw [weylParameter_retraction_eq (fam.l I) c (fam.isCompatible Q).levi hπ hπ']

end StandardParabolicFamily

end Langlands.Global
