import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.ActionDescent

/-! # Central cocharacters under fpqc quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {H Q : GroupScheme S}

/-- A cocharacter is central if its universal orbit is constant. -/
theorem centralizer_eq_top_of_orbit_id (χ : (Gm S).toGrp ⟶ Q)
    (hχ : orbit χ (𝟙 Q.X) = fst Q.X (Gm S).X) :
    centralizer χ = ⊤ := by
  have hid : 𝟙 Q.X ∈ (centralizer χ).carrier Q.X := by
    simpa only [mem_centralizer, Category.comp_id] using hχ
  apply SubgroupFunctor.ext
  intro T
  apply top_unique
  intro g _
  simpa only [Category.comp_id] using (centralizer χ).comp_mem g hid

/-- The image of a central cocharacter is central if the ambient map remains
epimorphic after product with the multiplicative group. -/
theorem centralizer_eq_top_comp_of_epi (χ : (Gm S).toGrp ⟶ H) (q : H ⟶ Q)
    [Epi (q.hom.hom ▷ (Gm S).X)] (hχ : centralizer χ = ⊤) :
    centralizer (χ ≫ q) = ⊤ := by
  apply centralizer_eq_top_of_orbit_id
  apply (cancel_epi (q.hom.hom ▷ (Gm S).X)).mp
  have h : orbit χ (𝟙 H.X) = fst H.X (Gm S).X := by
    apply (mem_centralizer χ).mp
    rw [hχ]
    exact Subgroup.mem_top _
  rw [whiskerRight_orbit, Category.comp_id, whiskerRight_fst]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using
    (orbit_comp_hom χ q (𝟙 H.X)).trans (congrArg (fun f => f ≫ q.hom.hom) h)

/-- A central cocharacter stays central under an fpqc homomorphism. -/
theorem centralizer_eq_top_comp_of_fpqc (χ : (Gm S).toGrp ⟶ H) (q : H ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hχ : centralizer χ = ⊤) : centralizer (χ ≫ q) = ⊤ := by
  have := AutomorphicAction.effectiveEpi_whiskerRight q (Gm S).X
  have : Epi (q.hom.hom ▷ (Gm S).X) := Over.epi_of_epi_left _
  exact centralizer_eq_top_comp_of_epi χ q hχ

/-- After an fpqc quotient, every point centralizes the image of a central
cocharacter; this equivalence retains the underlying quotient-group point. -/
def centralQuotientPointsEquiv (χ : (Gm S).toGrp ⟶ H) (q : H ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hχ : centralizer χ = ⊤) (T : Over S) :
    (T ⟶ Q.X) ≃* (centralizer (χ ≫ q)).carrier T where
  toFun g := ⟨g, by
    rw [centralizer_eq_top_comp_of_fpqc χ q hχ]
    exact Subgroup.mem_top _⟩
  invFun g := g.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem centralQuotientPointsEquiv_apply_coe
    (χ : (Gm S).toGrp ⟶ H) (q : H ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hχ : centralizer χ = ⊤) (T : Over S) (g : T ⟶ Q.X) :
    (centralQuotientPointsEquiv χ q hχ T g : T ⟶ Q.X) = g :=
  rfl

/-- If cocharacters lift along an fpqc quotient, centrality of all cocharacters
in the source implies centrality of all cocharacters in the quotient. -/
theorem central_cocharacters_of_fpqc_of_lifts (q : H ⟶ Q)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hlift : ∀ ψ : (Gm S).toGrp ⟶ Q, ∃ χ : (Gm S).toGrp ⟶ H, χ ≫ q = ψ)
    (hcentral : ∀ χ : (Gm S).toGrp ⟶ H, centralizer χ = ⊤) :
    ∀ ψ : (Gm S).toGrp ⟶ Q, centralizer ψ = ⊤ := by
  intro ψ
  obtain ⟨χ, rfl⟩ := hlift ψ
  exact centralizer_eq_top_comp_of_fpqc χ q (hcentral χ)

end Langlands.GroupScheme.Dynamic
