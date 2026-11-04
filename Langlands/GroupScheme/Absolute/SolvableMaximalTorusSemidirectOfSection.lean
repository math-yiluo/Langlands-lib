import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectStatement
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement
import Langlands.GroupScheme.Absolute.SolvableSplitExtensionStatement
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient
import Langlands.GroupScheme.Rational.SolvableMaximalTorusStatement
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.LeviMultiplication
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Torus complements in solvable groups from a section of the torus quotient

Let `H` be a smooth connected solvable affine group over an algebraically closed field, with
a fppf quotient `q : H ⟶ D` onto a split torus whose kernel is a closed unipotent subgroup
`i : U ⟶ H`. If `q` has a homomorphic section `σ : D ⟶ H` and maximal tori of `H` are
conjugate, then every maximal torus `s : T ⟶ H` maps isomorphically onto `D`, and the
multiplication `U × T ⟶ H` is an isomorphism of schemes. Combined with the existence of the
quotient, this gives Milne 2017, Theorem 16.33(d), conditionally on the section, the
conjugacy of maximal tori in solvable groups, closed subgroups of unipotent groups being
unipotent, and splitting of tori.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section General

variable {S : Scheme.{u}}

/-- A split torus, regarded as a commutative group scheme. -/
def IsSplitTorus.toCommGroupScheme {D : GroupScheme S} (hD : IsSplitTorus D) :
    CommGroupScheme S :=
  { D with comm := hD.isCommMonObj }

@[simp]
theorem IsSplitTorus.toCommGroupScheme_toGrp {D : GroupScheme S} (hD : IsSplitTorus D) :
    hD.toCommGroupScheme.toGrp = D := rfl

/-- Points of a split torus commute. -/
theorem IsSplitTorus.points_mul_comm {D : GroupScheme S} (hD : IsSplitTorus D) {T : Over S}
    (x y : T ⟶ D.X) : x * y = y * x := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hD
  apply (isoPointsEquiv e T).injective
  rw [map_mul, map_mul, mul_comm]

/-- Inner automorphisms of a split torus are trivial. -/
theorem IsSplitTorus.innerIso_hom {D : GroupScheme S} (hD : IsSplitTorus D)
    (g : Over.mk (𝟙 S) ⟶ D.X) : (D.innerIso g).hom = 𝟙 D := by
  apply hom_ext_points
  intro T x
  rw [comp_innerIso_hom, hD.points_mul_comm (D.constantPoint g T) x, mul_assoc,
    mul_inv_cancel, mul_one]
  rfl

/-- A homomorphism to a split torus is invariant under inner automorphisms of its source. -/
theorem innerIso_hom_comp_of_isSplitTorus {H D : GroupScheme S} (hD : IsSplitTorus D)
    (q : H ⟶ D) (g : Over.mk (𝟙 S) ⟶ H.X) : (H.innerIso g).hom ≫ q = q := by
  rw [innerIso_hom_comp, hD.innerIso_hom, Category.comp_id]

end General

section Field

variable {k : Type u} [Field k]

/-- If the scheme kernel of a homomorphism `q` to a split torus has the points of `i`, then
every unipotent subgroup is contained in `i`. -/
theorem range_le_of_isUnipotent_of_isSplitTorus
    {H U D W : GroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ H} {q : H ⟶ D}
    (hD : IsSplitTorus D) (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (w : W ⟶ H) (hW : IsUnipotent W) :
    SubgroupFunctor.range w ≤ SubgroupFunctor.range i := by
  intro V x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  rw [← hq, mem_range_kernelι_iff, Category.assoc, ← Grp.comp_hom_hom]
  exact hW.comp_eq_one_of_isSplitTorus hD (w ≫ q) V y

/-- A closed split torus meets a closed unipotent subgroup trivially on every test scheme,
granted that closed subgroups of unipotent groups are unipotent. -/
theorem range_inf_eq_bot_of_isSplitTorus_of_isUnipotent
    (hunip : UnipotentClosedSubgroupStatement.{u})
    {H U : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]
    (t : T.toGrp ⟶ H) (ht : IsClosedSubgroup t) (hT : IsSplitTorus T.toGrp)
    (i : U ⟶ H) (hU : IsUnipotent U) :
    SubgroupFunctor.range t ⊓ SubgroupFunctor.range i = ⊥ := by
  have hsnd : IsClosedSubgroup (subgroupIntersectionSnd t i) := by
    have : IsClosedImmersion t.hom.hom.left := ht
    have : IsClosedImmersion (subgroupIntersectionSnd t i).hom.hom.left :=
      MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme t i) this
    exact this
  have hW : IsUnipotent (subgroupIntersection t i) :=
    hunip k U (subgroupIntersection t i) _ hsnd hU
  apply le_antisymm
  swap
  · intro V p hp
    beta_reduce at hp ⊢
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hp
    subst hp
    exact Subgroup.one_mem _
  intro V p hp
  beta_reduce at hp ⊢
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  have hp' : p ∈ (SubgroupFunctor.range (subgroupIntersectionHom t i)).carrier V := by
    rw [range_subgroupIntersectionHom]
    exact hp
  obtain ⟨r, rfl⟩ := SubgroupFunctor.mem_range.1 hp'
  change r ≫ (subgroupIntersectionFst t i).hom.hom ≫ t.hom.hom = 1
  rw [← Category.assoc, hW.comp_eq_one_of_isSplitTorus hT (subgroupIntersectionFst t i) V r,
    MonObj.one_comp]

/-- A homomorphic section of a homomorphism of separated group schemes is a closed subgroup. -/
theorem IsClosedSubgroup.of_comp_eq_id {H D : GroupScheme (Spec (CommRingCat.of k))}
    [IsSeparated H.X.hom] (σ : D ⟶ H) (q : H ⟶ D) (h : σ ≫ q = 𝟙 D) :
    IsClosedSubgroup σ := by
  have : IsSeparated q.hom.hom.left := by
    have : IsSeparated (q.hom.hom.left ≫ D.X.hom) := by
      rw [Over.w]
      infer_instance
    exact IsSeparated.of_comp _ D.X.hom
  have : IsClosedImmersion (σ.hom.hom.left ≫ q.hom.hom.left) := by
    have h' : σ.hom.hom.left ≫ q.hom.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, h]
      rfl
    rw [h']
    infer_instance
  exact IsClosedImmersion.of_comp σ.hom.hom.left q.hom.hom.left

variable {H U D : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
  {i : U ⟶ H} {q : H ⟶ D}

/-- Let `q : H ⟶ D` be a homomorphism onto a split torus whose scheme kernel has the points
of a closed unipotent subgroup `i`, and let `σ` be a homomorphic section of `q`. If the
maximal tori of the solvable group `H` are conjugate and all split, then every maximal torus
`s` of `H` maps isomorphically onto `D` by `q`. -/
theorem isIso_comp_of_section [IsAlgClosed k]
    (hunip : UnipotentClosedSubgroupStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hconj : SolvableMaximalTorusConjugacyStatement.{u}) (hH : IsSolvableGroupScheme H)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (hD : IsSplitTorus D)
    (σ : D ⟶ H) (hσ : σ ≫ q = 𝟙 D)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (s : T.toGrp ⟶ H) (hs : IsMaximalTorus s) :
    IsIso (s ≫ q) := by
  have : IsAffineHom U.X.hom := hi.isAffineHom
  have : LocallyOfFiniteType U.X.hom := hi.locallyOfFiniteType
  -- A maximal torus through the image of the section.
  obtain ⟨T₀, t₀, ht₀, a, ha⟩ := exists_maximalTorus_extension_of_finiteType H
    (T := hD.toCommGroupScheme) σ hD.isTorus (IsClosedSubgroup.of_comp_eq_id σ q hσ)
  have hint := range_inf_eq_bot_of_isSplitTorus_of_isUnipotent hunip t₀ ht₀.2.1
    (IsTorus.isSplitTorus_of_finiteGaloisSplitting hsplit ht₀.1) i hU
  have : Mono t₀.hom.hom.left := ht₀.2.1.mono
  have hmono : Mono (t₀ ≫ q).hom.hom :=
    mono_comp_of_inf_eq_bot (Over.mono_of_mono_left _) hq hint
  have : Mono (t₀ ≫ q) := (Grp.forget _).mono_of_mono_map hmono
  have : IsSplitEpi (t₀ ≫ q) :=
    IsSplitEpi.mk' ⟨a, (Category.assoc a t₀ q).symm.trans ((congrArg (· ≫ q) ha).trans hσ)⟩
  have : IsIso (t₀ ≫ q) := isIso_of_mono_of_isSplitEpi _
  -- Conjugate `s` onto `t₀`; the quotient map does not see the conjugation.
  obtain ⟨g, e, hge⟩ := hconj k H hH T T₀ s t₀ hs ht₀
  have hsq : s ≫ q = e.hom ≫ t₀ ≫ q :=
    calc s ≫ q = s ≫ (H.innerIso g).hom ≫ q := by
          rw [innerIso_hom_comp_of_isSplitTorus hD q g]
      _ = e.hom ≫ t₀ ≫ q := by rw [← Category.assoc, hge, Category.assoc]
  rw [hsq]
  infer_instance

/-- Under the hypotheses of `isIso_comp_of_section`, multiplication `U × T ⟶ H`,
`(v, t) ↦ i(v) s(t)`, is an isomorphism of schemes for every maximal torus `s`. -/
theorem isIso_subgroupMultiplication_of_section [IsAlgClosed k]
    (hunip : UnipotentClosedSubgroupStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hconj : SolvableMaximalTorusConjugacyStatement.{u}) (hH : IsSolvableGroupScheme H)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (hD : IsSplitTorus D)
    (σ : D ⟶ H) (hσ : σ ≫ q = 𝟙 D)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (s : T.toGrp ⟶ H) (hs : IsMaximalTorus s) :
    IsIso (subgroupMultiplication i s) := by
  have := isIso_comp_of_section hunip hsplit hconj hH hi hU hq hD σ hσ s hs
  have : Mono i.hom.hom := by
    have : Mono i.hom.hom.left := hi.mono
    exact Over.mono_of_mono_left _
  have := isIso_subgroupMultiplication_of_isIso_comp (s := s) this hq
  exact (isIso_subgroupMultiplication_reverse_iff s i).1 this

end Field

/-- Existence of a split torus quotient with unipotent kernel (Milne 16.33(a), (c)), a
homomorphic section of that quotient (Milne 16.26(a)), conjugacy of maximal tori in smooth
connected solvable groups, closed subgroups of unipotent groups being unipotent, and
splitting of tori together give Milne 2017, Theorem 16.33(d). -/
theorem solvableMaximalTorusSemidirectStatement_of_section
    (hquot : SolvableTorusQuotientStatement.{u})
    (hsec : SolvableSplitExtensionStatement.{u})
    (hconj : SolvableMaximalTorusConjugacyStatement.{u})
    (hunip : UnipotentClosedSubgroupStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    SolvableMaximalTorusSemidirectStatement.{u} := by
  intro k _ _ H _ _ _ hH T s hs
  obtain ⟨U, D, i, q, hi, hUs, hUc, hU, hn, hfppf, hD⟩ := hquot k H hH
  obtain ⟨σ, hσ⟩ := hsec k H hH U D i q hi hUs hUc hU hn hfppf hD
  have hq := hfppf.2.2.2
  exact ⟨U, i, hi, hUs, hUc, hU, hn,
    fun W w _ hW => range_le_of_isUnipotent_of_isSplitTorus hD hq w hW,
    isIso_subgroupMultiplication_of_section hunip hsplit hconj hH hi hU hq hD σ hσ s hs⟩

end Langlands.GroupScheme
