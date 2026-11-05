import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Identifying supplied quotients by full dynamic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)
  (Q : Over S) (q : G.X ⟶ Q)

/-- An epimorphic quotient identifying every pair of points is the base scheme.
The inverse of its structure morphism is the image of the group identity. -/
def fullQuotientIso [Epi q.left]
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X), g ≫ q = h ≫ q) :
    Q ≅ Over.mk (𝟙 S) := by
  let p : Q ⟶ Over.mk (𝟙 S) :=
    Over.homMk Q.hom (Category.comp_id _)
  let e : Over.mk (𝟙 S) ⟶ Q := (1 : Over.mk (𝟙 S) ⟶ G.X) ≫ q
  letI : Epi q := Over.epi_of_epi_left q
  have hp : p ≫ e = 𝟙 Q := by
    apply (cancel_epi q).mp
    simpa only [e, Category.assoc, Category.comp_id, Category.id_comp] using
      hf G.X (q ≫ p ≫ (1 : Over.mk (𝟙 S) ⟶ G.X)) (𝟙 G.X)
  have he : e ≫ p = 𝟙 (Over.mk (𝟙 S)) := by
    apply Over.OverMorphism.ext
    change e.left ≫ Q.hom = 𝟙 S
    exact Over.w e
  exact ⟨p, e, hp, he⟩

/-- The structure morphism of the same supplied full quotient is an isomorphism. -/
theorem isIso_of_full_quotient [Epi q.left]
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X), g ≫ q = h ≫ q) :
    IsIso Q.hom := by
  let e := fullQuotientIso G Q q hf
  exact (Over.forget S).map_isIso e.hom

/-- The same supplied full quotient is proper over its base. -/
theorem isProper_of_full_quotient [Epi q.left]
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X), g ≫ q = h ≫ q) :
    IsProper Q.hom := by
  let _ := isIso_of_full_quotient G Q q hf
  infer_instance

namespace Dynamic

variable {G Q}

/-- The supplied quotient by a full dynamic parabolic is canonically the base.
Smoothness, surjectivity and quasi-compactness provide the epimorphism needed
to identify the actual quotient model. -/
def suppliedQuotientIsoOfParabolicEqTop
    (χ : (Gm S).toGrp ⟶ G) [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hP : parabolic χ = ⊤)
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (parabolic χ).carrier T) :
    Q ≅ Over.mk (𝟙 S) :=
  fullQuotientIso G Q q (by
    intro T g h
    apply (hf T g h).mpr
    rw [hP]
    exact Subgroup.mem_top _)

/-- Properness holds for the actual supplied quotient whenever the dynamic
parabolic is the full subgroup. No reductivity or field hypothesis is needed. -/
theorem suppliedQuotient_isProper_of_parabolic_eq_top
    (χ : (Gm S).toGrp ⟶ G) [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hP : parabolic χ = ⊤)
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (parabolic χ).carrier T) :
    IsProper Q.hom := by
  let e := suppliedQuotientIsoOfParabolicEqTop q χ hP hf
  let _ : IsIso Q.hom := (Over.forget S).map_isIso e.hom
  infer_instance

/-- In particular every supplied quotient for the trivial cocharacter is proper. -/
theorem suppliedQuotient_isProper_trivialCocharacter
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (parabolic (trivialCocharacter G)).carrier T) :
    IsProper Q.hom :=
  suppliedQuotient_isProper_of_parabolic_eq_top q _
    (parabolic_trivialCocharacter (G := G)) hf

/-- A cocharacter centralizing the whole group also gives a proper supplied quotient. -/
theorem suppliedQuotient_isProper_of_centralizer_eq_top
    (χ : (Gm S).toGrp ⟶ G) [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hχ : centralizer χ = ⊤)
    (hf : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (parabolic χ).carrier T) :
    IsProper Q.hom :=
  suppliedQuotient_isProper_of_parabolic_eq_top q χ
    (parabolic_eq_top_of_centralizer χ hχ) hf

end Dynamic
end Langlands.GroupScheme
