import Langlands.GroupScheme.HomScheme.AdmissibleClosedRepresentability
import Langlands.AlgebraicGeometry.ClosedSubschemeGluing

/-! # Effective Zariski descent of closed subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- An actual closed group scheme representing a subgroup on every test. -/
structure ClosedRepresentative (F : SubgroupFunctor G) where
  group : GroupScheme S
  hom : group ⟶ G
  represents : F.IsRepresentedBy hom
  closed : IsClosedSubgroup hom

namespace ClosedRepresentative

/-- Choose actual representative data from closed representability. -/
def ofIsClosedRepresentable {F : SubgroupFunctor G}
    (hF : F.IsClosedRepresentable) : ClosedRepresentative F where
  group := hF.choose
  hom := hF.choose_spec.choose
  represents := hF.choose_spec.choose_spec.1
  closed := hF.choose_spec.choose_spec.2

end ClosedRepresentative

variable (F : SubgroupFunctor G)

/-- Local closed subgroup representatives represent absolute membership over
the induced cover of the ambient scheme. -/
theorem exists_localClosedSubscheme_of_isClosedRepresentable
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, (F.baseChange (𝒰.f i)).IsClosedRepresentable) (i : 𝒰.I₀) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ (𝒰.pullback₁ G.X.hom).X i),
      IsClosedImmersion j ∧
        ∀ (Y : Scheme.{u}) (a : Y ⟶ (𝒰.pullback₁ G.X.hom).X i),
          F.schemeCondition (a ≫ (𝒰.pullback₁ G.X.hom).f i) ↔
            ∃ b : Y ⟶ Z, b ≫ j = a := by
  let r := ClosedRepresentative.ofIsClosedRepresentable (h i)
  refine ⟨r.group.X.left, r.hom.hom.hom.left, r.closed, ?_⟩
  intro Y a
  exact (F.schemeCondition_baseChange_iff (𝒰.f i) a).trans
    (schemeCondition_iff_exists_of_isRepresentedBy
      (G := (GroupScheme.baseChange (𝒰.f i)).obj G)
      (F.baseChange (𝒰.f i)) r.represents a)

/-- Closed representability is local on the base for a Zariski-local subgroup
condition, with no smoothness or affineness hypotheses. -/
theorem isClosedRepresentable_of_openCover (hF : IsZariskiLocal F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, (F.baseChange (𝒰.f i)).IsClosedRepresentable) :
    F.IsClosedRepresentable := by
  choose L c hc hL using F.exists_localClosedSubscheme_of_isClosedRepresentable 𝒰 h
  let 𝒱 : G.X.left.OpenCover := 𝒰.pullback₁ G.X.hom
  obtain ⟨L₀, c₀, hc₀, hfac⟩ :=
    Scheme.ClosedSubschemeGluing.exists_isClosedImmersion
      (P := fun _ x => F.schemeCondition x)
      (fun _ _ a z hz => F.schemeCondition_comp z a hz)
      (fun i : 𝒰.I₀ => 𝒱.f i) c (fun i _ z => hL i _ z)
      (fun x => ⟨𝒱.idx x, 𝒱.covers x⟩)
      (fun Z z hz => by
        choose U hU hPU using hz
        let 𝒲 : Z.OpenCover := Scheme.Cover.mkOfCovers Z (fun p => (U p : Scheme.{u}))
          (fun p => (U p).ι) (fun p => ⟨p, ⟨p, hU p⟩, rfl⟩)
        exact (F.schemeCondition_iff_openCover hF z 𝒲).mpr hPU)
  letI : IsClosedImmersion c₀ := hc₀
  exact F.isClosedRepresentable_of_schemeCondition c₀ (fun _ x => hfac x)

/-- Choose the actual closed subgroup obtained by gluing locally closed
representatives of a Zariski-local membership condition. -/
def closedRepresentativeOfOpenCover (hF : IsZariskiLocal F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, (F.baseChange (𝒰.f i)).IsClosedRepresentable) :
    ClosedRepresentative F :=
  ClosedRepresentative.ofIsClosedRepresentable
    (F.isClosedRepresentable_of_openCover hF 𝒰 h)

variable (𝒰 : Scheme.OpenCover.{u} S)
    (H : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj G))

/-- A matching family of closed subgroup functors descends to a closed
subgroup functor. -/
theorem isClosedRepresentable_descentSubgroup (hH : IsMatching 𝒰 H)
    (hc : ∀ i, (H i).IsClosedRepresentable) :
    (descentSubgroup 𝒰 H).IsClosedRepresentable := by
  apply (descentSubgroup 𝒰 H).isClosedRepresentable_of_openCover
    (isZariskiLocal_descentSubgroup 𝒰 H (fun i => by
      obtain ⟨K, j, hj, _⟩ := hc i
      exact hj.isZariskiLocal)) 𝒰
  intro i
  rw [baseChange_descentSubgroup 𝒰 H hH i]
  exact hc i

/-- The actual closed group scheme obtained from matching closed subgroups. -/
def closedRepresentativeOfMatching (hH : IsMatching 𝒰 H)
    (hc : ∀ i, (H i).IsClosedRepresentable) :
    ClosedRepresentative (descentSubgroup 𝒰 H) :=
  ClosedRepresentative.ofIsClosedRepresentable
    (isClosedRepresentable_descentSubgroup 𝒰 H hH hc)

end Langlands.GroupScheme.SubgroupFunctor
