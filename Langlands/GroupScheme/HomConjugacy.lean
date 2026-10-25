import Langlands.GroupScheme.InnerAutomorphism

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
universe u
variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Base-point pullback is a group homomorphism. -/
def constantPointHom (T : Over S) : (Over.mk (𝟙 S) ⟶ G.X) →* (T ⟶ G.X) :=
  (G.points.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 S)).op).hom

@[simp] theorem constantPointHom_apply (T : Over S) (g : Over.mk (𝟙 S) ⟶ G.X) :
    G.constantPointHom T g = G.constantPoint g T := rfl

@[simp] theorem constantPoint_self (g : Over.mk (𝟙 S) ⟶ G.X) :
    G.constantPoint g (Over.mk (𝟙 S)) = g := by
  change (𝟙 (Over.mk (𝟙 S))) ≫ g = g
  exact Category.id_comp g

variable {G} {H : GroupScheme S}

/-- Inner conjugacy of group-scheme morphisms by a point over the base. -/
def HomConjugate (χ ψ : H ⟶ G) : Prop :=
  ∃ g : Over.mk (𝟙 S) ⟶ G.X, χ ≫ (G.innerIso g).hom = ψ

/-- Scheme conjugacy is equivalent to conjugacy by one base point on every test scheme. -/
theorem homConjugate_iff_points (χ ψ : H ⟶ G) :
    HomConjugate χ ψ ↔ ∃ g : Over.mk (𝟙 S) ⟶ G.X,
      ∀ (T : Over S) (x : T ⟶ H.X),
        G.constantPoint g T * (x ≫ χ.hom.hom) * (G.constantPoint g T)⁻¹ =
          x ≫ ψ.hom.hom := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun T x => ?_⟩
    have h := congrArg (fun f : H ⟶ G => x ≫ f.hom.hom) hg
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom] at h
    exact h
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply hom_ext_points
    intro T x
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
    exact hg T x

/-- Every group-scheme morphism is conjugate to itself. -/
theorem HomConjugate.refl (χ : H ⟶ G) : HomConjugate χ χ := by
  apply (homConjugate_iff_points χ χ).mpr
  refine ⟨1, fun T x => ?_⟩
  have h := (G.constantPointHom T).map_one
  simp only [constantPointHom_apply] at h
  simp [h]

/-- Reversing a scheme conjugacy uses the inverse base point. -/
theorem HomConjugate.symm {χ ψ : H ⟶ G} (h : HomConjugate χ ψ) :
    HomConjugate ψ χ := by
  obtain ⟨g, hg⟩ := (homConjugate_iff_points χ ψ).mp h
  apply (homConjugate_iff_points ψ χ).mpr
  refine ⟨g⁻¹, fun T x => ?_⟩
  have hi := (G.constantPointHom T).map_inv g
  simp only [constantPointHom_apply] at hi
  rw [hi, ← hg T x]
  group

/-- Composing scheme conjugacies multiplies their base points in the corresponding order. -/
theorem HomConjugate.trans {χ ψ ξ : H ⟶ G}
    (h : HomConjugate χ ψ) (h' : HomConjugate ψ ξ) : HomConjugate χ ξ := by
  obtain ⟨g, hg⟩ := (homConjugate_iff_points χ ψ).mp h
  obtain ⟨g', hg'⟩ := (homConjugate_iff_points ψ ξ).mp h'
  apply (homConjugate_iff_points χ ξ).mpr
  refine ⟨g' * g, fun T x => ?_⟩
  have hm := (G.constantPointHom T).map_mul g' g
  simp only [constantPointHom_apply] at hm
  rw [hm, ← hg' T x, ← hg T x]
  group

/-- The equivalence relation defining inner conjugacy classes of group-scheme morphisms. -/
def homConjugacySetoid (H G : GroupScheme S) : Setoid (H ⟶ G) where
  r := HomConjugate
  iseqv := ⟨HomConjugate.refl, HomConjugate.symm, HomConjugate.trans⟩

end Langlands.GroupScheme
