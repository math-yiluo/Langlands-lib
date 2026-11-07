import Langlands.Representation.Exponents.LeviCuspidalEmbeddingStatement
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.FullParabolicLeviFunctors
import Langlands.GroupScheme.Rational.IdentityParabolic
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Unconditional steps towards Renard VI.2.1 for actual represented parabolics

Renard VI.2.1, Corollary and proof (printed p.139 / PDF p.145), chooses a parabolic that
is minimal among those with a nonzero Jacquet module, shows that its Jacquet module is
supercuspidal, takes an irreducible quotient and embeds the representation into the
induced representation by Frobenius reciprocity. This module proves the steps of that
argument which need neither represented transitivity nor parabolic extension nor finite
type:

* a closed subgroup `q` of a closed subgroup `j` whose composite has the range of `j` is
  an isomorphism;
* strict inclusion of all-test ranges of closed subgroups of an affine group of finite
  type over a field is well founded, through the kernel ideals in the Noetherian
  coordinate ring; hence a nonempty family of actual parabolic data has a member with
  minimal range;
* the identity parabolic has a nonzero Jacquet module, so there is an actual parabolic
  datum with nonzero Jacquet module and minimal range among those;
* at a datum whose Jacquet module is nonzero, finitely generated and supercuspidal, an
  irreducible quotient is supercuspidal and the representation embeds into its
  induction.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

namespace IsClosedSubgroup

/-- If the composite of closed subgroups `q ≫ j` has at least the all-test range of `j`,
then `q` is an isomorphism. -/
theorem isIso_of_range_le_range_comp {Q M : GroupScheme (Spec (CommRingCat.of k))}
    {q : Q ⟶ M} {j : M ⟶ G} (hq : IsClosedSubgroup q) (hj : IsClosedSubgroup j)
    (h : SubgroupFunctor.range j ≤ SubgroupFunctor.range (q ≫ j)) : IsIso q := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion q.hom.hom.left := hq
  have : IsClosedImmersion (q ≫ j).hom.hom.left := hq.comp hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono q.hom.hom := Over.mono_of_mono_left _
  have : Mono (q ≫ j).hom.hom := Over.mono_of_mono_left _
  let f := SubgroupFunctor.factorOfRangeLE h
  have hf : f ≫ q ≫ j = j := SubgroupFunctor.factorOfRangeLE_comp h
  have h₁ : f ≫ q = 𝟙 M := by
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).1
    rw [← Grp.comp_hom_hom, Category.assoc, hf, Grp.id_hom_hom, Category.id_comp]
  have h₂ : q ≫ f = 𝟙 Q := by
    apply Grp.hom_ext
    apply (cancel_mono q.hom.hom).1
    rw [← Grp.comp_hom_hom, Category.assoc, h₁, Category.comp_id, Grp.id_hom_hom,
      Category.id_comp]
  exact ⟨f, h₂, h₁⟩

/-- Strict inclusion of the all-test ranges of closed subgroups of an affine group
reverses into strict inclusion of their kernel ideals in the coordinate ring. -/
theorem ker_ideal_lt_of_range_lt [IsAffine G.X.left]
    {H H' : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G} {i' : H' ⟶ G}
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hlt : SubgroupFunctor.range i < SubgroupFunctor.range i') :
    i'.hom.hom.left.ker.ideal ⟨⊤, isAffineOpen_top G.X.left⟩ <
      i.hom.hom.left.ker.ideal ⟨⊤, isAffineOpen_top G.X.left⟩ := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let f := SubgroupFunctor.factorOfRangeLE hlt.le
  have hf : f ≫ i' = i := SubgroupFunctor.factorOfRangeLE_comp hlt.le
  have hfs : f.hom.hom.left ≫ i'.hom.hom.left = i.hom.hom.left :=
    congrArg (fun z : H ⟶ G => z.hom.hom.left) hf
  have hk : i'.hom.hom.left.ker ≤ i.hom.hom.left.ker := by
    rw [← hfs]
    exact Scheme.Hom.le_ker_comp _ _
  refine lt_of_le_of_ne (hk _) fun heq => hlt.ne (le_antisymm hlt.le ?_)
  have hker : i.hom.hom.left.ker = i'.hom.hom.left.ker :=
    Scheme.IdealSheafData.ext_of_isAffine heq.symm
  have : IsIso f.hom.hom.left :=
    IsClosedImmersion.isIso_of_ker_eq _ _ _ hfs hker
  have : IsIso f.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp
      (show IsIso f.hom.hom.left from inferInstance)
  have : IsIso f.hom :=
    (isIso_iff_of_reflects_iso _ (Mon.forget _)).mp
      (show IsIso f.hom.hom from inferInstance)
  have : IsIso f :=
    (isIso_iff_of_reflects_iso _ (Grp.forget₂Mon _)).mp
      (show IsIso f.hom from inferInstance)
  exact SubgroupFunctor.range_le_of_factor (inv f) ((IsIso.inv_comp_eq f).mpr hf.symm)

end IsClosedSubgroup

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]

/-- An actual rational parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`, matching
geometric unipotent radical `r : U ⟶ P` and Levi-radical multiplication isomorphism:
the data quantified in `LeviCuspidalEmbeddingStatement`, bundled so that they can be
compared by the all-test range of `p`. -/
structure ParabolicDatum (G : GroupScheme (Spec (CommRingCat.of k))) where
  /-- The parabolic group scheme. -/
  P : GroupScheme (Spec (CommRingCat.of k))
  /-- The Levi group scheme. -/
  M : GroupScheme (Spec (CommRingCat.of k))
  /-- The unipotent radical group scheme. -/
  U : GroupScheme (Spec (CommRingCat.of k))
  /-- The inclusion of the parabolic. -/
  p : P ⟶ G
  /-- The inclusion of the Levi into the parabolic. -/
  l : M ⟶ P
  /-- The inclusion of the radical into the parabolic. -/
  r : U ⟶ P
  hp : IsParabolicSubgroup p
  hl : IsRationalLeviSubgroup l
  hr : LeviSubgroup.IsGeometricUnipotentRadical r
  hmul : IsIso (subgroupMultiplication l r)

namespace ParabolicDatum

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The identity parabolic of a connected reductive group, with Levi the identity and
radical the unit subgroup. -/
def identity (hG : IsConnectedReductive G) : ParabolicDatum G where
  P := G
  M := G
  U := Grp.trivial _
  p := 𝟙 G
  l := 𝟙 G
  r := kernelUnit G
  hp := hG.isParabolicSubgroup_id
  hl := hG.isRationalLeviSubgroup_id
  hr := hG.isGeometricUnipotentRadical_kernelUnit
  hmul := isIso_subgroupMultiplication_id_kernelUnit

/-- In an affine group of finite type over a field, every nonempty family of actual
parabolic data has a member whose parabolic has minimal all-test range: the kernel ideals
of the parabolics in the Noetherian coordinate ring have a maximal element. -/
theorem exists_minimal [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : ParabolicDatum G → Prop) (hS : ∃ D, S D) :
    ∃ D, S D ∧ ∀ D', S D' → ¬ SubgroupFunctor.range D'.p < SubgroupFunctor.range D.p := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let U : G.X.left.affineOpens := ⟨⊤, isAffineOpen_top G.X.left⟩
  have : IsNoetherianRing Γ(G.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian U
  let ideals : Set (Ideal Γ(G.X.left, ⊤)) :=
    {I | ∃ D, S D ∧ D.p.hom.hom.left.ker.ideal U = I}
  obtain ⟨D₀, hD₀⟩ := hS
  obtain ⟨I, ⟨D, hD, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian Γ(G.X.left, ⊤) Γ(G.X.left, ⊤)) ideals ⟨_, D₀, hD₀, rfl⟩
  refine ⟨D, hD, fun D' hD' hlt => hmax _ ⟨D', hD', rfl⟩ ?_⟩
  exact IsClosedSubgroup.ker_ideal_lt_of_range_lt D'.hp.isClosedSubgroup
    D.hp.isClosedSubgroup hlt

end ParabolicDatum

/-- The normalized Jacquet functor preserves actual surjections. -/
theorem normalizedJacquetFunctor_map_surjective {H : Type u} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H] (N L : Subgroup H)
    (hN : IsClosed (N : Set H)) (hLN : L ≤ Subgroup.normalizer (N : Set H))
    {A B : SmoothRep.{0, u, v} ℂ H} (f : A ⟶ B) (hf : Function.Surjective (SmoothRep.hom f)) :
    Function.Surjective (SmoothRep.hom ((normalizedJacquetFunctor N L hN hLN).map f)) := by
  intro y
  obtain ⟨b, rfl⟩ := Jacquet.Localization.mk_surjective B.representation N 1 y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Jacquet.Localization.mk A.representation N 1 a,
    normalizedJacquetFunctor_map_mk N L hN hLN f a⟩

/-- There is an actual parabolic datum with nonzero normalized Jacquet module whose
parabolic has minimal all-test range among the data with nonzero Jacquet module. The
identity parabolic, whose Jacquet module is the representation itself, shows that the
family is nonempty. -/
theorem exists_minimal_nontrivial_leviJacquet :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)), Nontrivial π →
        ∃ D : ParabolicDatum G,
          Nontrivial ((leviJacquetFunctor.{u, v} D.p D.l D.r D.hp D.hr D.hl D.hmul).obj π) ∧
          ∀ D' : ParabolicDatum G, SubgroupFunctor.range D'.p < SubgroupFunctor.range D.p →
            Subsingleton
              ((leviJacquetFunctor.{u, v} D'.p D'.l D'.r D'.hp D'.hr D'.hl D'.hmul).obj π) := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hπ
  have := hG.smooth
  let D₁ := ParabolicDatum.identity hG
  have : IsIso D₁.p := inferInstanceAs (IsIso (𝟙 G))
  have h₁ : Nontrivial
      ((leviJacquetFunctor.{u, v} D₁.p D₁.l D₁.r D₁.hp D₁.hr D₁.hl D₁.hmul).obj π) :=
    (fullParabolicLeviJacquetEquiv D₁.p D₁.l D₁.hp D₁.hl hG D₁.r D₁.hr D₁.hmul
      π).toLinearEquiv.toEquiv.nontrivial
  obtain ⟨D, hD, hmin⟩ := ParabolicDatum.exists_minimal
    (fun D => Nontrivial
      ((leviJacquetFunctor.{u, v} D.p D.l D.r D.hp D.hr D.hl D.hmul).obj π)) ⟨D₁, h₁⟩
  exact ⟨D, hD, fun D' hlt =>
    not_nontrivial_iff_subsingleton.mp fun h => hmin D' h hlt⟩

/-- Renard VI.2.1, proof, final step: at an actual parabolic datum whose normalized
Jacquet module `J` is nonzero, finitely generated over `ℂ[M(F)]` and supercuspidal for
every proper actual parabolic of `M`, an irreducible quotient `ρ` of `J` is
supercuspidal, and Frobenius reciprocity turns the quotient map into an injective
intertwiner from the irreducible `π` to the induction of `ρ`. -/
theorem cuspidalEmbedding_of_finite_supercuspidal :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        π.IsIrreducible →
        ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
          (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
          (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
          (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
          (hmul : IsIso (subgroupMultiplication l r)),
          haveI := hl.isConnectedReductive.isAffineHom
          letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
          haveI : LocallyCompactSpace (rationalPoints M) :=
            leviPoints_locallyCompactSpace p l hp hl
          haveI : NonarchimedeanGroup (rationalPoints M) :=
            leviPoints_nonarchimedeanGroup p l hp hl
          let J := (leviJacquetFunctor.{u, v} p l r hp hr hl hmul).obj π
          Nontrivial J →
          Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) J.representation.asModule →
          (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
            (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
            (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
            (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
            (hmul' : IsIso (subgroupMultiplication l' r')),
            ¬ IsIso p' →
              Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj J)) →
          ∃ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
            ρ.IsIrreducible ∧
            (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
              (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
              (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
              (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
              (hmul' : IsIso (subgroupMultiplication l' r')),
              ¬ IsIso p' →
                Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) ∧
            (∃ q : J.representation.IntertwiningMap ρ.representation,
              Function.Surjective q) ∧
            ∃ f : π.representation.IntertwiningMap
                ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj ρ).representation,
              Function.Injective f := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π hπ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro J hJ hfin hcusp
  -- A maximal proper subrepresentation of the finitely generated nonzero `J`.
  have hco : IsCoatomic (Subrepresentation J.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := J.representation)).isCoatomic_iff.mpr inferInstance
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subrepresentation J.representation, IsCoatom T₀ := by
    rcases hco.eq_top_or_exists_le_coatom ⊥ with hbot | ⟨T₀, hT₀, -⟩
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : J)
      apply hy
      have hmem : y ∈ (⊥ : Subrepresentation J.representation) := by
        rw [hbot]
        exact Submodule.mem_top
      exact hmem
    · exact ⟨T₀, hT₀⟩
  let ρ := SmoothRep.quotient J T₀
  have hρ : ρ.IsIrreducible :=
    SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom J T₀ hT₀
  let q : J ⟶ ρ := SmoothRep.mkQ J T₀
  have hq : Function.Surjective (SmoothRep.hom q) := SmoothRep.mkQ_surjective J T₀
  refine ⟨ρ, hρ, ?_, ⟨SmoothRep.hom q, hq⟩, ?_⟩
  · -- Normalized Jacquet restriction preserves the surjection `J → ρ`.
    intro P' M' U' p' l' r' hp' hl' hr' hmul' hne
    have := hcusp P' M' U' p' l' r' hp' hl' hr' hmul' hne
    exact (normalizedJacquetFunctor_map_surjective _ _ _ _ q hq).subsingleton
  · -- Frobenius reciprocity and irreducibility of `π`.
    obtain ⟨e, -⟩ :=
      leviFrobeniusReciprocity.{u, v, v} k G hG P M U p l r hp hl hr hmul π ρ
    let F := e.symm (SmoothRep.hom q)
    have hF : F ≠ 0 := by
      intro hF0
      have : Nontrivial ρ.representation.asModule :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints M)) _
      obtain ⟨s, hs⟩ := exists_ne (0 : ρ.representation.asModule)
      obtain ⟨y, hy⟩ := hq s
      apply hs
      have hq0 : SmoothRep.hom q = 0 := by
        have h := congrArg e hF0
        simpa [F] using h
      rw [← hy, hq0]
      rfl
    have : π.representation.IsIrreducible := hπ
    exact ⟨F, (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

end Langlands.Aubert.General.RepresentedParabolic
