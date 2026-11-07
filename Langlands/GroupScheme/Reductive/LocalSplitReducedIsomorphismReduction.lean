import Langlands.GroupScheme.Reductive.LocalSplitFieldPoints
import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus
import Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.LinearAlgebra.RootDatumBaseExists

/-! # The Isomorphism Theorem over a reduced local ring, assuming root groups exist -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

open CoordinateRootDatum LocalSplitBigCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Over every field point, the field comparison theorem gives an isomorphism of point groups
matching the tori and the Weyl families built from the simple-root data. -/
theorem exists_fieldPointsEquiv_of_simpleRoots (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i')
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hP' : IsFibrewiseRootDatumOf I H i' P) (b : P.Base) (W : ∀ α, SimpleWord P b α)
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hw : ∀ a ∈ b.support,
      IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a))
    (hu' : ∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) ∧
      IsRootParametrization i' (P.root (P.reflectionPerm a a)) (u' (P.reflectionPerm a a)))
    (hw' : ∀ a ∈ b.support,
      IsWeylPoint i' (weylPoint (u' a) (u' (P.reflectionPerm a a))) (P.reflection a))
    (K : Type u) [Field K] [Algebra R K] :
    ∃ Ψ : (fieldPoint R K ⟶ G.X) ≃* (fieldPoint R K ⟶ H.X),
      (∀ t : fieldPoint R K ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
        Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) ∧
      ∀ α c, Ψ (rootPoint (weylFamily P W u α) _ c) = rootPoint (weylFamily P W u' α) _ c := by
  classical
  have := hG.smooth
  have := hH.smooth
  have := hP.finite
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R K)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R K)))
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R K)).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R K)))
  let bK : (fieldRealization K P).Base := b.map (fieldRealizationEquiv K P)
  have hmem : ∀ a, a ∈ bK.support → a ∈ b.support := by
    intro a ha
    rw [RootPairing.Base.support_map_eq, Finset.mem_image] at ha
    obtain ⟨a', h', rfl⟩ := ha
    exact h'
  have hmem' : ∀ a, a ∈ b.support → a ∈ bK.support := by
    intro a ha
    rw [RootPairing.Base.support_map_eq, Finset.mem_image]
    exact ⟨a, ha, rfl⟩
  have hneg : ∀ a, P.root (P.reflectionPerm a a) = -P.root a := by
    intro a
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  obtain ⟨Φ, hΦ, hΦs⟩ := exists_iso_of_simpleRootParametrizations
    (hG.isConnectedReductive_algebraMap K) (hH.isConnectedReductive_algebraMap K)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax K)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I H i' hmax' K)
    hP.isReduced (hP.field K) (hP'.field K) bK
    (u := fun a => baseChangeRoot K (u a))
    (v := fun a => baseChangeRoot K (u (P.reflectionPerm a a)))
    (u' := fun a => baseChangeRoot K (u' a))
    (v' := fun a => baseChangeRoot K (u' (P.reflectionPerm a a)))
    (fun a ha => isRootParametrization_baseChangeRoot K i _ _ (hu a (hmem a ha)).1)
    (fun a ha => by
      have h := isRootParametrization_baseChangeRoot K i _ _ (hu a (hmem a ha)).2
      rwa [hneg] at h)
    (fun a ha => ((hw a (hmem a ha)).baseChange K).mem_normalizerPoints)
    (fun a ha => isRootParametrization_baseChangeRoot K i' _ _ (hu' a (hmem a ha)).1)
    (fun a ha => by
      have h := isRootParametrization_baseChangeRoot K i' _ _ (hu' a (hmem a ha)).2
      rwa [hneg] at h)
    (fun a ha => ((hw' a (hmem a ha)).baseChange K).mem_normalizerPoints)
  exact exists_fieldPointsEquiv K Φ hΦ P W
    (fun a T c => baseChangePointsEquiv_rootPoint K (u a) T c)
    (fun a T c => baseChangePointsEquiv_rootPoint K (u' a) T c)
    (fun a ha => (hΦs a (hmem' a ha)).1) (fun a ha => (hΦs a (hmem' a ha)).2)

omit [IsAffineHom G.X.hom] in
/-- Root parametrizations of the simple roots and their negatives with Weyl-normalized simple
Weyl points extend to root parametrizations of all roots, keeping the given ones at `±a`. -/
theorem exists_rootParametrizations_of_simple [Finite J] {P : RootDatum J (I → ℤ) (I → ℤ)}
    [P.IsReduced] (b : P.Base) {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u : J → (Ga R ⟶ G)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hw : ∀ a ∈ b.support,
      IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)) :
    ∃ u' : J → (Ga R ⟶ G), (∀ α, IsRootParametrization i (P.root α) (u' α)) ∧
      ∀ a ∈ b.support,
        IsWeylPoint i (weylPoint (u' a) (u' (P.reflectionPerm a a))) (P.reflection a) := by
  classical
  let W : ∀ α, SimpleWord P b α := fun α => (nonempty_simpleWord P b α).some
  let u' : J → (Ga R ⟶ G) := fun α =>
    if α ∈ b.support ∨ ∃ a ∈ b.support, α = P.reflectionPerm a a then u α
    else weylFamily P W u α
  have hs : ∀ a ∈ b.support, u' a = u a := fun a ha => ite_eq_left (Or.inl ha)
  have hn : ∀ a ∈ b.support, u' (P.reflectionPerm a a) = u (P.reflectionPerm a a) :=
    fun a ha => ite_eq_left (Or.inr ⟨a, ha, rfl⟩)
  refine ⟨u', fun α => ?_, fun a ha => ?_⟩
  · by_cases h : α ∈ b.support ∨ ∃ a ∈ b.support, α = P.reflectionPerm a a
    · rw [show u' α = u α from ite_eq_left h]
      rcases h with h | ⟨a, ha, rfl⟩
      · exact (hu α h).1
      · exact (hu a ha).2
    · rw [show u' α = weylFamily P W u α from ite_eq_right h]
      exact isRootParametrization_weylFamily (fun a ha => (hu a ha).1) hw W α
  · rw [hs a ha, hn a ha]
    exact hw a ha

/-- **The common-torus case.** Two reductive groups over a reduced local ring with closed
coordinate split tori on the same `I`, maximal on all residue fibres, and with the same
fibrewise root datum are isomorphic, provided root groups exist
(`LocalSplitRootGroupStatement`). -/
theorem nonempty_iso_of_commonTorus (hRG : LocalSplitRootGroupStatement.{u})
    [IsLocalRing R] [IsReduced R] (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} (hi : IsClosedSubgroup i)
    (hi' : IsClosedSubgroup i')
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i')
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hP' : IsFibrewiseRootDatumOf I H i' P) : Nonempty (G ≅ H) := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b⟩ := Langlands.LinearAlgebra.RootDatumBase.nonempty_base P
  obtain ⟨u, hu, hw⟩ := hRG R G hG I i hi hmax J P hP b
  obtain ⟨u', hu', hw'⟩ := hRG R H hH I i' hi' hmax' J P hP' b
  let W : ∀ α, SimpleWord P b α := fun α => (nonempty_simpleWord P b α).some
  have hû := isRootParametrization_weylFamily (fun a _ => hu a) hw W
  have hû' := isRootParametrization_weylFamily (fun a _ => hu' a) hw' W
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  have := localSplitBigCell R G hG I i hi hmax J P hP b (weylFamily P W u) hû _ _ neg pos
  have := localSplitBigCell R H hH I i' hi' hmax' J P hP' b (weylFamily P W u') hû' _ _ neg pos
  exact nonempty_iso_of_fieldAlgebras hG hH (fun k => (neg k : J)) (fun k => (pos k : J))
    (fun K _ _ => exists_fieldPointsEquiv_of_simpleRoots hG hH hmax hmax' hP hP' b W
      (fun a _ => ⟨hu a, hu (P.reflectionPerm a a)⟩) hw
      (fun a _ => ⟨hu' a, hu' (P.reflectionPerm a a)⟩) hw' K)

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme

open LocalSplitCell

/-- **The Isomorphism Theorem over a reduced local ring**, assuming the existence of root
groups (`LocalSplitRootGroupStatement`). -/
theorem localSplitReducedIsomorphismTheorem_of_rootGroups
    (hRG : LocalSplitRootGroupStatement.{u}) :
    LocalSplitReducedIsomorphismTheoremStatement.{u} := by
  intro R _ _ _ G H _ _ hG hH I I' _ _ i i' hi hi' hmax hmax' J J' P Q hP hQ ⟨e⟩
  classical
  exact nonempty_iso_of_commonTorus hRG hG hH hi (isClosedSubgroup_precompTorus e.weightEquiv hi')
    hmax (isFibrewiseMaximalTorus_precompTorus e.weightEquiv hmax') hP
    (isFibrewiseRootDatumOf_precompTorus hP hQ e)

/-- **Root groups at the simple roots over a reduced local ring.** In the setting of
`LocalSplitRootGroupStatement`, for every base `b` there are root parametrizations of the simple
roots `a` and of their negatives `-a = P.reflectionPerm a a`, such that for every simple `a` the
Weyl point `u_{-a}(-1) u_a(1) u_{-a}(-1)` acts on the torus by the simple reflection `s_a`. -/
def LocalSplitSimpleRootGroupStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsReduced R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      (∀ s : Spec (CommRingCat.of R),
        IsMaximalTorus
          (T := (CommGroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
              (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
          ((GroupScheme.baseChange
            ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i)) →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ b : P.Base, ∃ u : J → (Ga R ⟶ G),
        (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
          IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) ∧
        ∀ a ∈ b.support,
          IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)

/-- Root groups at the simple roots and their negatives give root groups for all roots. -/
theorem localSplitRootGroup_of_simple (h : LocalSplitSimpleRootGroupStatement.{u}) :
    LocalSplitRootGroupStatement.{u} := by
  intro R _ _ _ G _ hG I _ _ i hi hmax J P hP b
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨u, hu, hw⟩ := h R G hG I i hi hmax J P hP b
  exact exists_rootParametrizations_of_simple b hu hw

/-- **The Isomorphism Theorem over a reduced local ring**, assuming the existence of root
groups at the simple roots (`LocalSplitSimpleRootGroupStatement`). -/
theorem localSplitReducedIsomorphismTheorem_of_simpleRootGroups
    (h : LocalSplitSimpleRootGroupStatement.{u}) :
    LocalSplitReducedIsomorphismTheoremStatement.{u} :=
  localSplitReducedIsomorphismTheorem_of_rootGroups (localSplitRootGroup_of_simple h)

end Langlands.GroupScheme
