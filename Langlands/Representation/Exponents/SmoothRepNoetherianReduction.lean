import Langlands.Representation.Exponents.SmoothRepNoetherianCategoryStatement
import Langlands.Representation.Exponents.LeviJacquetFiniteTypeStatement
import Langlands.Representation.Exponents.RepresentedCuspidalRemainderSplittingStatement
import Langlands.Representation.Exponents.RepresentedCuspidalProjection
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingSteps
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Geometric.SelfIntersectionLevi
import Langlands.Representation.Category.ExactFunctor
import Langlands.Representation.Category.RenardNoetherian
import Langlands.CategoryTheory.Renard.FiniteFamilyNoetherian
import Langlands.GroupScheme.Lie.DimensionInduction

/-! # Noetherianity of `M(G)` from four explicit inputs

Renard VI.7.5, Proposition, is reduced to four statements, by induction on the Lie
dimension of `G`. Two inputs are already published statements: Renard VI.1.3 (normalized
Jacquet modules of finite-type representations are of finite type) and the objectwise
cuspidal/remainder splitting from VI.3.5. Two inputs are stated here: finite-type
supercuspidal representations are Noetherian, and supercuspidality is tested on finitely
many proper parabolics. None of the four is proved here.
-/

noncomputable section

universe u v

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Finite-type supercuspidal representations are Noetherian: for every connected
reductive `G`, a supercuspidal smooth representation finitely generated over `ℂ[G(F)]`
is a Noetherian `ℂ[G(F)]`-module. -/
def SupercuspidalFiniteTypeNoetherianStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsSupercuspidal A →
        Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) A.representation.asModule →
          IsNoetherian (MonoidAlgebra ℂ (rationalPoints G)) A.representation.asModule

/-- Supercuspidality is tested on finitely many proper parabolics: for every connected
reductive `G` there are finitely many proper actual rational parabolic data such that
every smooth representation whose normalized Jacquet modules along them all vanish is
supercuspidal. -/
def FiniteProperParabolicSupercuspidalTestStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)],
      ∃ (n : ℕ) (D : Fin n → ParabolicDatum G), (∀ i, ¬ IsIso (D i).p) ∧
        ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G),
          (∀ i, Subsingleton ((jacquetFunctor (D i).p (D i).l (D i).r (D i).hp (D i).hr
            (D i).hl (D i).hmul).obj A)) → IsSupercuspidal A

/-- The conclusion of the Proposition for one connected reductive group: its smooth
representations form a Noetherian category in Renard's sense. -/
def SmoothRepNoetherianAt (k : Type u) [Field k] [TopologicalSpace k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) : Prop :=
  haveI := hG.isAffineHom
  letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)],
    Langlands.Renard.IsNoetherianCategory (SmoothRep.{0, u, v} ℂ (rationalPoints G))

section LieDimension

variable {k : Type u} [Field k]

/-- The Levi of a proper parabolic of a connected reductive group has strictly smaller
Lie dimension. -/
theorem lieDimension_levi_lt {G P M : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (p : P ⟶ G) (l : M ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hproper : ¬ IsIso p) :
    @Lie.dimension k _ M hl.isConnectedReductive.isAffineHom <
      @Lie.dimension k _ G hG.isAffineHom := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have := hl.isConnectedReductive.isAffineHom
  have := hl.isConnectedReductive.smooth
  refine Lie.dimension_lt_of_proper_closedSubgroup (l ≫ p)
    (hl.isClosedSubgroup.comp hp.isClosedSubgroup) fun h => ?_
  exact hproper (hp.isClosedSubgroup.isIso_of_isIso_comp l)

end LieDimension

section Family

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance noetherianReductionPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The transported normalized Jacquet functor preserves monomorphisms. -/
theorem leviJacquetFunctor_preservesMonomorphisms (hG : IsConnectedReductive G)
    {P M U : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    (leviJacquetFunctor.{u, v} p l r hp hr hl hmul).PreservesMonomorphisms := by
  let := leviPointTopology l hl
  obtain ⟨-, hex⟩ := leviParabolicFunctorsExact.{u, v} k G hG P M U p l r hp hl hr hmul
  refine ⟨fun {A B} f hf => ?_⟩
  apply (SmoothRep.mono_iff_injective _).mpr
  exact (hex f (SmoothRep.cokernelπ f)
    (SmoothRep.isShortExact_cokernelπ f ((SmoothRep.mono_iff_injective f).mp hf))).1

/-- A group with a topology, indexing the targets of the heterogeneous finite family. -/
structure PointGroup where
  carrier : Type u
  [group : Group carrier]
  [topology : TopologicalSpace carrier]

attribute [local instance] PointGroup.group PointGroup.topology

variable {n : ℕ} (D : Fin n → ParabolicDatum G)

/-- The groups of the family: `G(F)` itself, then the Levi points of each datum. -/
def pointGroups : Option (Fin n) → PointGroup.{u}
  | none => ⟨rationalPoints G⟩
  | some i => @PointGroup.mk (rationalPoints (D i).M) _ (leviPointTopology (D i).l (D i).hl)

variable (hs : ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G), HasCuspidalRemainderSplitting A)

/-- The family: the supercuspidal part, then the transported Jacquet functors. -/
def familyFunctor : ∀ j : Option (Fin n),
    SmoothRep.{0, u, v} ℂ (rationalPoints G) ⥤ SmoothRep.{0, u, v} ℂ (pointGroups D j).carrier
  | none => cuspidalPartFunctor hs
  | some i => leviJacquetFunctor (D i).p (D i).l (D i).r (D i).hp (D i).hr (D i).hl (D i).hmul

theorem familyFunctor_preservesMonomorphisms (hG : IsConnectedReductive G) :
    ∀ j, (familyFunctor D hs j).PreservesMonomorphisms
  | none => (inferInstance : (cuspidalPartFunctor hs).PreservesMonomorphisms)
  | some i => leviJacquetFunctor_preservesMonomorphisms hG (D i).p (D i).l (D i).r (D i).hp
      (D i).hl (D i).hr (D i).hmul

/-- If the Jacquet functors along the data test supercuspidality, the family jointly
reflects isomorphisms between monomorphisms. -/
theorem familyFunctor_jointlyReflectsMonoIsos (hG : IsConnectedReductive G)
    (htest : ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G),
      (∀ i, Subsingleton ((jacquetFunctor (D i).p (D i).l (D i).r (D i).hp (D i).hr
        (D i).hl (D i).hmul).obj A)) → IsSupercuspidal A) :
    Langlands.Renard.JointlyReflectsMonoIsos (familyFunctor D hs) := by
  intro A B f hf hiso
  have hinj : Function.Injective (SmoothRep.hom f) := (SmoothRep.mono_iff_injective f).mp hf
  have hseq := SmoothRep.isShortExact_cokernelπ f hinj
  -- Every Jacquet module of the cokernel vanishes.
  have hJ : ∀ i, Subsingleton ((jacquetFunctor (D i).p (D i).l (D i).r (D i).hp (D i).hr
      (D i).hl (D i).hmul).obj (SmoothRep.cokernel f)) := by
    intro i
    let := leviPointTopology (D i).l (D i).hl
    obtain ⟨-, hex⟩ := leviParabolicFunctorsExact.{u, v} k G hG (D i).P (D i).M (D i).U
      (D i).p (D i).l (D i).r (D i).hp (D i).hl (D i).hr (D i).hmul
    have hexf := hex f (SmoothRep.cokernelπ f) hseq
    have : IsIso ((leviJacquetFunctor.{u, v} (D i).p (D i).l (D i).r (D i).hp (D i).hr
        (D i).hl (D i).hmul).map f) := hiso (some i)
    have hsurj : Function.Surjective (SmoothRep.hom ((leviJacquetFunctor.{u, v} (D i).p
        (D i).l (D i).r (D i).hp (D i).hr (D i).hl (D i).hmul).map f)) :=
      (SmoothRep.epi_iff_surjective _).mp inferInstance
    have hzero : ∀ y : (leviJacquetFunctor.{u, v} (D i).p (D i).l (D i).r (D i).hp (D i).hr
        (D i).hl (D i).hmul).obj (SmoothRep.cokernel f), y = 0 := by
      intro y
      obtain ⟨b, rfl⟩ := hexf.2.1 y
      have hb : b ∈ LinearMap.ker (SmoothRep.hom ((leviJacquetFunctor.{u, v} (D i).p (D i).l
          (D i).r (D i).hp (D i).hr (D i).hl (D i).hmul).map
            (SmoothRep.cokernelπ f))).toLinearMap := by
        rw [← hexf.2.2]
        obtain ⟨a, ha⟩ := hsurj b
        exact ⟨a, ha⟩
      exact hb
    exact ⟨fun a b => by rw [hzero a, hzero b]⟩
  have hQ : IsSupercuspidal (SmoothRep.cokernel f) := htest _ hJ
  -- The supercuspidal part of the cokernel vanishes.
  have h0 : IsZero ((cuspidalPartFunctor hs).obj (SmoothRep.cokernel f)) := by
    have : IsIso ((cuspidalPartFunctor hs).map f) := hiso none
    have : Epi (SmoothRep.cokernelπ f) := (SmoothRep.epi_iff_surjective _).mpr hseq.2.1
    have hc : (cuspidalPartFunctor hs).map (SmoothRep.cokernelπ f) = 0 := by
      rw [← cancel_epi ((cuspidalPartFunctor hs).map f), ← Functor.map_comp,
        SmoothRep.comp_cokernelπ, Functor.map_zero, comp_zero]
    exact IsZero.of_epi_eq_zero _ hc
  have hQz : IsZero (SmoothRep.cokernel f) :=
    isZero_of_isSupercuspidal_of_isZero_cuspidalPartFunctor_obj hs hQ h0
  have : Subsingleton (SmoothRep.cokernel f) := (SmoothRep.isZero_iff_subsingleton _).mp hQz
  have hsurjf : Function.Surjective (SmoothRep.hom f) := by
    intro b
    have hb : b ∈ LinearMap.ker (SmoothRep.hom (SmoothRep.cokernelπ f)).toLinearMap := by
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    rw [← hseq.2.2] at hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, ha⟩
  have : Epi f := (SmoothRep.epi_iff_surjective f).mpr hsurjf
  exact isIso_of_mono_of_epi f

end Family

section Reduction

attribute [local instance] PointGroup.group PointGroup.topology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]

/-- The inductive step: if the Levi of every proper parabolic of `G` has a Noetherian
category of smooth representations, so does `G`, given the four inputs. -/
theorem smoothRepNoetherianAt_of_levis
    (h1 : LeviJacquetFiniteTypeStatement.{u, v})
    (h2 : RepresentedCuspidalRemainderSplittingStatement.{u, v})
    (h3 : SupercuspidalFiniteTypeNoetherianStatement.{u, v})
    (h4 : FiniteProperParabolicSupercuspidalTestStatement.{u, v})
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (ih : ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → ∀ hl : IsRationalLeviSubgroup l, ¬ IsIso p →
        SmoothRepNoetherianAt.{u, v} k M hl.isConnectedReductive) :
    SmoothRepNoetherianAt.{u, v} k G hG := by
  have := hG.isAffineHom
  let _ : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  unfold SmoothRepNoetherianAt
  intro _ _
  refine ⟨SmoothRep.hasAllSubobjectUnions, fun X hX => ?_⟩
  have hs := h2 k G hG
  obtain ⟨n, D, hDp, htest⟩ := h4 k G hG
  have hfin : Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) X.representation.asModule :=
    (SmoothRep.renardFiniteType_iff X).mp hX
  have := familyFunctor_preservesMonomorphisms D hs hG
  refine Langlands.Renard.noetherianObject_of_finite_family (familyFunctor D hs)
    (familyFunctor_jointlyReflectsMonoIsos D hs hG htest) X fun j => ?_
  cases j with
  | none =>
    have hπ : Function.Surjective (SmoothRep.hom ((cuspidalPartπ hs).app X)) :=
      (SmoothRep.epi_iff_surjective _).mp inferInstance
    have : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
        ((𝟭 (SmoothRep.{0, u, v} ℂ (rationalPoints G))).obj X).representation.asModule := hfin
    have hfin0 : Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
        ((cuspidalPartFunctor hs).obj X).representation.asModule :=
      Module.Finite.of_surjective (Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (SmoothRep.hom ((cuspidalPartπ hs).app X))) hπ
    exact (SmoothRep.renardNoetherian_iff _).mpr
      (h3 k G hG _ (isSupercuspidal_cuspidalPartFunctor_obj hs X) hfin0)
  | some i =>
    let := leviPointTopology (D i).l (D i).hl
    have := leviPoints_locallyCompactSpace (D i).p (D i).l (D i).hp (D i).hl
    have := leviPoints_nonarchimedeanGroup (D i).p (D i).l (D i).hp (D i).hl
    have hfinM := h1 k G hG (D i).P (D i).M (D i).U (D i).p (D i).l (D i).r (D i).hp (D i).hl
      (D i).hr (D i).hmul X hfin
    have hM : Langlands.Renard.IsNoetherianCategory
        (SmoothRep.{0, u, v} ℂ (rationalPoints (D i).M)) :=
      ih (D i).P (D i).M (D i).p (D i).l (D i).hp (D i).hl (hDp i)
    exact hM.2 _ ((SmoothRep.renardFiniteType_iff _).mpr hfinM)

/-- Renard VI.7.5, Proposition, from four explicit inputs: Renard VI.1.3 for Jacquet
modules, the objectwise cuspidal/remainder splitting of VI.3.5, Noetherianity of
finite-type supercuspidal representations, and a finite proper-parabolic supercuspidality
test. The proof is by strong induction on the Lie dimension of `G`. -/
theorem smoothRepNoetherianCategory_of_inputs
    (h1 : LeviJacquetFiniteTypeStatement.{u, v})
    (h2 : RepresentedCuspidalRemainderSplittingStatement.{u, v})
    (h3 : SupercuspidalFiniteTypeNoetherianStatement.{u, v})
    (h4 : FiniteProperParabolicSupercuspidalTestStatement.{u, v}) :
    SmoothRepNoetherianCategoryStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  show SmoothRepNoetherianAt.{u, v} k G hG
  suffices key : ∀ (d : ℕ) (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G), @Lie.dimension k _ G hG.isAffineHom = d →
        SmoothRepNoetherianAt.{u, v} k G hG from
    @key _ G hG rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro G hG hd
    refine smoothRepNoetherianAt_of_levis h1 h2 h3 h4 G hG fun P M p l hp hl hproper => ?_
    exact ih _ ((lieDimension_levi_lt hG p l hp hl hproper).trans_eq hd) M
      hl.isConnectedReductive rfl

end Reduction

end Langlands.Aubert.General.RepresentedParabolic
