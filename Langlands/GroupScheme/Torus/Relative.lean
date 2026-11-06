import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.Descent.Data
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Étale forms of split tori over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorus

variable {S S' : Scheme.{u}} {G H : GroupScheme S}

/-- An actual group scheme which becomes a finite split torus on an étale
cover of the base. The rank may vary between members of the cover. -/
def IsTorus (G : GroupScheme S) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
    ∀ i : 𝒰.I₀, IsSplitTorus ((GroupScheme.baseChange (𝒰.f i)).obj G)

/-- Split tori are étale forms of split tori, using the identity cover. -/
theorem IsTorus.of_isSplitTorus (hG : IsSplitTorus G) : IsTorus G :=
  ⟨Scheme.coverOfIsIso (P := @Etale) (𝟙 S),
    fun _ => hG.baseChange (𝟙 S)⟩

/-- The relative-torus property is invariant under actual group-scheme
isomorphisms over the base. -/
theorem IsTorus.of_iso (e : G ≅ H) (hH : IsTorus H) : IsTorus G := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  exact ⟨𝒰, fun i => IsSplitTorus.of_iso ((GroupScheme.baseChange (𝒰.f i)).mapIso e) (h𝒰 i)⟩

/-- Étale forms of split tori remain such after arbitrary base change. -/
theorem IsTorus.baseChange (b : S' ⟶ S) (hG : IsTorus G) :
    IsTorus ((GroupScheme.baseChange b).obj G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰.pullback₁ b, fun i => ?_⟩
  change IsSplitTorus
    ((GroupScheme.baseChange (pullback.fst b (𝒰.f i))).obj ((GroupScheme.baseChange b).obj G))
  let e :=
    Descent.pullbackComparison b (pullback.fst b (𝒰.f i))
      (pullback.snd b (𝒰.f i) ≫ 𝒰.f i) pullback.condition G ≪≫
      baseChangeCompIso (𝒰.f i) (pullback.snd b (𝒰.f i)) G
  exact IsSplitTorus.of_iso e ((h𝒰 i).baseChange (pullback.snd b (𝒰.f i)))

end Langlands.GroupScheme.RelativeTorus
