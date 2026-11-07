import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.RationalPointEtaleLiftProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasSchemeCompatibilityProof

/-!
# Chart maps of the étale-chart topology

Over a henselian valued field `K`, maps `h_U → X` from schemes `U` locally of finite type
to an algebraic space `X` over `Spec K` induce maps `U(K) → X(K)`. These are open for the
étale-chart topology when the map is étale (the first step of Conrad's proof of
Proposition 5.4, printed p.15), and continuous whenever the rational points of `X` are
covered by charts, which holds for quasi-separated `X` locally of finite type.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField schemePointContinuity_proof
    henselianEtalePointLocalHomeomorph)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

section PresheafPullback

variable {S : Scheme.{u}}

/-- Two compatible sections of a pullback square of presheaves come from a section of
the pullback. -/
theorem exists_app_of_isPullback {P A B C : Presheaf S} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) (T : Over S)
    (a : A.obj (op T)) (b : B.obj (op T)) (hab : f.app (op T) a = g.app (op T) b) :
    ∃ p : P.obj (op T), fst.app (op T) p = a ∧ snd.app (op T) p = b :=
  Types.exists_of_isPullback (h.map ((evaluation _ _).obj (op T))) a b hab

/-- Sections of the pullback of a pullback square of presheaves are determined by their
two projections. -/
theorem ext_app_of_isPullback {P A B C : Presheaf S} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) (T : Over S)
    {p q : P.obj (op T)} (h₁ : fst.app (op T) p = fst.app (op T) q)
    (h₂ : snd.app (op T) p = snd.app (op T) q) : p = q :=
  Types.ext_of_isPullback (h.map ((evaluation _ _).obj (op T))) h₁ h₂

end PresheafPullback

variable {K : Type u} [NontriviallyNormedField K]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- The map on rational points induced by a map `a : h_U → X` from an actual scheme. -/
def schemePointsMap {U : Over (Spec (CommRingCat.of K))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) : RingPoint K U K → RingPoints K X K :=
  fun x => a.app (op (PointTopology.ringTest K K)) (ULift.up x)

section PairPullback

variable {U V : Over (Spec (CommRingCat.of K))} (a : (schemeYoneda _).obj U ⟶ X.presheaf)
variable (b : (schemeYoneda _).obj V ⟶ X.presheaf)

/-- The represented pullback of two maps `a : h_U → X` and `b : h_V → X` from schemes. -/
abbrev pairPullback : Over (Spec (CommRingCat.of K)) :=
  (X.representable_from_scheme a).pullback b

/-- The projection of `pairPullback a b` to `V`. -/
abbrev pairPullbackSnd : pairPullback a b ⟶ V :=
  (X.representable_from_scheme a).snd b

/-- The projection of `pairPullback a b` to `U`. -/
def pairPullbackFst : pairPullback a b ⟶ U :=
  (schemeYoneda _).preimage ((X.representable_from_scheme a).fst b)

theorem pairPullback_isPullback :
    IsPullback ((schemeYoneda _).map (pairPullbackFst a b))
      ((schemeYoneda _).map (pairPullbackSnd a b)) a b := by
  rw [pairPullbackFst, Functor.map_preimage]
  exact (X.representable_from_scheme a).isPullback b

theorem etale_pairPullbackFst (hb : IsEtale b) : Etale (pairPullbackFst a b).left :=
  hb.projection a _ _ (pairPullback_isPullback a b).flip

theorem etale_pairPullbackSnd (ha : IsEtale a) : Etale (pairPullbackSnd a b).left :=
  ha.projection b _ _ ((X.representable_from_scheme a).isPullback b)

theorem locallyOfFiniteType_pairPullback [LocallyOfFiniteType U.hom] (hb : IsEtale b) :
    LocallyOfFiniteType (pairPullback a b).hom := by
  have := etale_pairPullbackFst a b hb
  rw [← Over.w (pairPullbackFst a b)]
  infer_instance

/-- Points of the pullback map to the same point of `X` through `a` and `b`. -/
theorem schemePointsMap_pairPullbackFst (w : RingPoint K (pairPullback a b) K) :
    schemePointsMap a (w ≫ pairPullbackFst a b) = schemePointsMap b (w ≫ pairPullbackSnd a b) :=
  congrArg (fun φ => φ.app (op (PointTopology.ringTest K K)) (ULift.up w))
    (pairPullback_isPullback a b).w

/-- Points of `U` and `V` with the same image in `X` come from a point of the pullback. -/
theorem exists_pairPullback_point {x : RingPoint K U K} {y : RingPoint K V K}
    (h : schemePointsMap a x = schemePointsMap b y) :
    ∃ w : RingPoint K (pairPullback a b) K,
      w ≫ pairPullbackFst a b = x ∧ w ≫ pairPullbackSnd a b = y := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_app_of_isPullback (pairPullback_isPullback a b)
    (PointTopology.ringTest K K) (ULift.up x) (ULift.up y) h
  exact ⟨p.down, congrArg ULift.down hp₁, congrArg ULift.down hp₂⟩

/-- Points of the pullback are determined by their two projections. -/
theorem pairPullback_point_ext {w w' : RingPoint K (pairPullback a b) K}
    (h₁ : w ≫ pairPullbackFst a b = w' ≫ pairPullbackFst a b)
    (h₂ : w ≫ pairPullbackSnd a b = w' ≫ pairPullbackSnd a b) : w = w' :=
  congrArg ULift.down (ext_app_of_isPullback (pairPullback_isPullback a b)
    (PointTopology.ringTest K K) (p := ULift.up w) (q := ULift.up w')
    (congrArg ULift.up h₁) (congrArg ULift.up h₂))

/-- The preimage under `b` of the image under `a` of a set of points of `U`. -/
theorem preimage_image_schemePointsMap (S : Set (RingPoint K U K)) :
    schemePointsMap b ⁻¹' (schemePointsMap a '' S) =
      (fun w : RingPoint K (pairPullback a b) K => w ≫ pairPullbackSnd a b) ''
        ((fun w : RingPoint K (pairPullback a b) K => w ≫ pairPullbackFst a b) ⁻¹' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨w, hw₁, hw₂⟩ := exists_pairPullback_point a b hxy
    exact ⟨w, (congrArg (· ∈ S) hw₁).mpr hx, hw₂⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, hw, schemePointsMap_pairPullbackFst a b w⟩

end PairPullback

/-- The chart map is the point map of the underlying transformation. -/
theorem EtaleFiniteTypeChart.pointMap_eq (c : EtaleFiniteTypeChart K X) :
    c.pointMap = schemePointsMap (AlgebraicSpace.hom c.hom) :=
  rfl

/-- **Étale maps from schemes are open on rational points** (Conrad, proof of
Proposition 5.4, printed p.15): over a henselian valued field, an étale map `h_U → X`
from a scheme locally of finite type induces an open map `U(K) → X(K)` for the
étale-chart topology. -/
theorem isOpenMap_schemePointsMap (hK : IsHenselianValuedField K)
    {U : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) :
    @IsOpenMap _ _ (schemePointTopology K U K) (etaleChartTopology K X)
      (schemePointsMap a) := by
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  intro V hV
  rw [etaleChartTopology_isOpen_iff]
  intro d
  let : TopologicalSpace (RingPoint K d.scheme K) := schemePointTopology K d.scheme K
  let : TopologicalSpace (RingPoint K (pairPullback a (hom d.hom)) K) :=
    schemePointTopology K _ K
  have e : d.pointMap ⁻¹' (schemePointsMap a '' V) = _ :=
    preimage_image_schemePointsMap a (hom d.hom) V
  rw [e]
  have := locallyOfFiniteType_pairPullback a (hom d.hom) d.isEtale
  have := d.locallyOfFiniteType
  have := etale_pairPullbackSnd a (hom d.hom) ha
  have hloc := henselianEtalePointLocalHomeomorph K hK (pairPullback a (hom d.hom)) d.scheme
    (pairPullbackSnd a (hom d.hom))
  exact hloc.isOpenMap _
    (hV.preimage (schemePointContinuity_proof K K _ _ (pairPullbackFst a (hom d.hom))))

/-- **Chart maps are open**: over a henselian valued field, the map from the rational
points of an étale chart of finite type to the rational points of the space is open for
the étale-chart topology. -/
theorem EtaleFiniteTypeChart.isOpenMap_pointMap (hK : IsHenselianValuedField K)
    (c : EtaleFiniteTypeChart K X) :
    @IsOpenMap _ _ (schemePointTopology K c.scheme K) (etaleChartTopology K X) c.pointMap :=
  have := c.locallyOfFiniteType
  isOpenMap_schemePointsMap hK (AlgebraicSpace.hom c.hom) c.isEtale

/-- A map `g` is continuous at the image of `x` under a local homeomorphism `h` when
`g ∘ h` is continuous at `x`. -/
theorem continuousAt_of_isLocalHomeomorph_comp {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {h : α → β} {g : β → γ}
    (hh : IsLocalHomeomorph h) (x : α) (hg : ContinuousAt (g ∘ h) x) :
    ContinuousAt g (h x) := by
  unfold ContinuousAt at hg ⊢
  rw [← hh.map_nhds_eq x, Filter.tendsto_map'_iff]
  exact hg

/-- The source of an étale map to a space locally of finite type is locally of finite
type. -/
theorem locallyOfFiniteType_of_isEtale (hX : LocallyOfFiniteTypeOverBase X)
    {U : Over (Spec (CommRingCat.of K))} (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (ha : IsEtale a) : LocallyOfFiniteType U.hom := by
  obtain ⟨V, b, hb, hbs, hV⟩ := hX.exists_atlas
  let hr := X.representable_from_scheme b
  obtain ⟨g, hg⟩ := (schemeYoneda _).map_surjective (hr.fst a)
  have hsq : IsPullback ((schemeYoneda _).map g) ((schemeYoneda _).map (hr.snd a)) b a := by
    rw [hg]
    exact hr.isPullback a
  have hs : Surjective (hr.snd a).left := hbs.projection a _ _ hsq
  have he : Etale (hr.snd a).left := hb.projection a _ _ hsq
  have hg' : Etale g.left := ha.projection b _ _ hsq.flip
  have : LocallyOfFiniteType ((hr.snd a).left ≫ U.hom) := by
    rw [Over.w (hr.snd a), ← Over.w g]
    infer_instance
  exact locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp _ _ _ _ _ hs
    inferInstance inferInstance this

/-- Every rational point of a quasi-separated space locally of finite type is the image of
a point of an étale chart of finite type (Knutson II.6.4, cited by Conrad on printed
p.15). -/
theorem exists_chart_pointMap_eq (hX : IsQuasiSeparated X)
    (hX' : LocallyOfFiniteTypeOverBase X) (x : RingPoints K X K) :
    ∃ (d : EtaleFiniteTypeChart K X) (y : RingPoint K d.scheme K), d.pointMap y = x := by
  obtain ⟨U, f, hU, hf, u, hu⟩ :=
    RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement K X hX x
  have hlft := locallyOfFiniteType_of_isEtale hX' (hom f) hf
  have := hU
  exact ⟨⟨U, f, hf, hlft, inferInstance⟩, u, hu⟩

/-- **Maps from schemes are continuous on rational points**: if every rational point of `X`
lies in the image of a chart, then every map `h_U → X` from a scheme locally of finite
type induces a continuous map `U(K) → X(K)` for the étale-chart topology. -/
theorem continuous_schemePointsMap (hK : IsHenselianValuedField K)
    (hcov : ∀ x : RingPoints K X K,
      ∃ (d : EtaleFiniteTypeChart K X) (y : RingPoint K d.scheme K), d.pointMap y = x)
    {U : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) :
    @Continuous _ _ (schemePointTopology K U K) (etaleChartTopology K X)
      (schemePointsMap a) := by
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨d, y, hy⟩ := hcov (schemePointsMap a x)
  obtain ⟨w, hw₁, -⟩ := exists_pairPullback_point a (hom d.hom) hy.symm
  let : TopologicalSpace (RingPoint K (pairPullback a (hom d.hom)) K) :=
    schemePointTopology K _ K
  let : TopologicalSpace (RingPoint K d.scheme K) := schemePointTopology K d.scheme K
  have := locallyOfFiniteType_pairPullback a (hom d.hom) d.isEtale
  have := etale_pairPullbackFst a (hom d.hom) d.isEtale
  have hloc := henselianEtalePointLocalHomeomorph K hK (pairPullback a (hom d.hom)) U
    (pairPullbackFst a (hom d.hom))
  have hcomp : Continuous (schemePointsMap a ∘
      fun w : RingPoint K (pairPullback a (hom d.hom)) K => w ≫ pairPullbackFst a (hom d.hom)) := by
    have : (schemePointsMap a ∘
        fun w : RingPoint K (pairPullback a (hom d.hom)) K => w ≫ pairPullbackFst a (hom d.hom)) =
          d.pointMap ∘ fun w : RingPoint K (pairPullback a (hom d.hom)) K => w ≫ pairPullbackSnd a (hom d.hom) :=
      funext (schemePointsMap_pairPullbackFst a (hom d.hom))
    rw [this]
    exact d.continuous_pointMap.comp (schemePointContinuity_proof K K _ _ _)
  have := continuousAt_of_isLocalHomeomorph_comp hloc w hcomp.continuousAt
  exact hw₁ ▸ this

end Langlands.AlgebraicGeometry.AlgebraicSpace
