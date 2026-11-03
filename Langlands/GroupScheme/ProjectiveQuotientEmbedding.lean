import Langlands.GroupScheme.ProjectiveDualLineChart
import Langlands.GroupScheme.ProjectiveLineStabilizerQuotient
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.GroupScheme.Dynamic.FlagQuotientAction
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Projective orbit maps on supplied homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix
open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

namespace Langlands.GroupScheme.ProjectiveOrbit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Sections

variable {n : ℕ} {R : CommRingCat.{u}}

/-- Pulling back the section of a test point along a test morphism gives the section of the
composite test point. -/
theorem pointSection_naturality {Z Z' : Over (Spec R)} (c : Z' ⟶ Z) (y : Z ⟶ ambient n R) :
    c.left ≫ pointSection y =
      pointSection (c ≫ y) ≫ RelativeProjectiveSpace.map n c.left := by
  apply RelativeProjectiveSpace.hom_ext <;> simp [pointSection]

/-- The matrix-translated section in the definition of matrix equivariance is natural in the
test scheme. -/
theorem pointSection_matrixAction_naturality {H : GroupScheme (Spec R)}
    (ρ : MatrixRepresentation H (Fin (n + 1))) {Z Z' : Over (Spec R)} (c : Z' ⟶ Z)
    (h : Z ⟶ H.X) (y : Z ⟶ ambient n R) :
    c.left ≫ pointSection y ≫ matrixAction n (ρ.pointMatrix Z h) ≫
        RelativeProjectiveSpace.map n Z.hom =
      pointSection (c ≫ y) ≫ matrixAction n (ρ.pointMatrix Z' (c ≫ h)) ≫
        RelativeProjectiveSpace.map n Z'.hom := by
  rw [reassoc_of% pointSection_naturality c y, map_matrixAction_assoc,
    ← ρ.pointMatrix_naturality, ← RelativeProjectiveSpace.map_comp, Over.w c]

/-- Matrix equivariance holds as soon as it holds for the universal test point. -/
theorem isMatrixEquivariant_of_universal {H : GroupScheme (Spec R)} {X : Over (Spec R)}
    (a : SchemeAction H X) (ρ : MatrixRepresentation H (Fin (n + 1)))
    (φ : X ⟶ ambient n R)
    (h₀ : (a.hom ≫ φ).left =
      pointSection (snd H.X X ≫ φ) ≫ matrixAction n (ρ.pointMatrix (H.X ⊗ X) (fst H.X X)) ≫
        RelativeProjectiveSpace.map n (H.X ⊗ X).hom) :
    IsMatrixEquivariant a ρ φ := by
  intro Z h x
  have key := pointSection_matrixAction_naturality ρ (lift h x) (fst H.X X) (snd H.X X ≫ φ)
  rw [← h₀, lift_fst, lift_snd_assoc] at key
  rw [← key, SchemeAction.act, Category.assoc, Over.comp_left]

variable {G : GroupScheme (Spec R)}

/-- The section of a point of an orbit map is the corresponding orbit section. -/
theorem pointSection_orbitMap (ρ : MatrixRepresentation G (Fin (n + 1)))
    (p : Spec R ⟶ RelativeProjectiveSpace (Spec R) n) {Z : Over (Spec R)} (g : Z ⟶ G.X) :
    pointSection (g ≫ orbitMap n ρ p) = orbitSection n ρ p Z g := by
  apply section_ext_of_map n Z.hom
  · simp [pointSection]
  · rw [pointSection_map, comp_orbitMap]

end Sections

section Quotient

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
variable (n : ℕ) (i : H ⟶ G) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1)))
variable (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
  x ∈ (SubgroupFunctor.range i).carrier T ↔
    ∃ c : Γ(T.left, ⊤)ˣ,
      (ρ.pointMatrix T x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
          Pi.single j 1 =
        (c : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) :
          Fin (n + 1) → Γ(T.left, ⊤)))
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)

/-- The orbit map of the `j`-th coordinate line. -/
abbrev lineOrbitMap : G.X ⟶ ambient n (CommRingCat.of k) :=
  orbitMap n ρ (RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) j)

include hρ hfib

/-- The coordinate-line orbit map descended through the supplied quotient. -/
def quotientOrbitMap : Q ⟶ ambient n (CommRingCat.of k) :=
  HomogeneousQuotientComparison.desc q (lineOrbitMap n j ρ)
    (fun T g h hgh => (basisSection_orbitMap_fibers n i j ρ hρ T g h).mpr ((hfib T g h).mp hgh))

@[reassoc]
theorem fac_quotientOrbitMap :
    q ≫ quotientOrbitMap n i j ρ hρ q hfib = lineOrbitMap n j ρ :=
  HomogeneousQuotientComparison.fac_desc _ _ _

/-- The descended orbit map is matrix equivariant for every action of `G` on the quotient
that is compatible with left multiplication. -/
theorem isMatrixEquivariant_quotientOrbitMap (a : SchemeAction G Q)
    (hact : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q) :
    IsMatrixEquivariant a ρ (quotientOrbitMap n i j ρ hρ q hfib) := by
  have hlift : ∀ (Z : Over (Spec (CommRingCat.of k))) (g y : Z ⟶ G.X),
      (a.act g (y ≫ q) ≫ quotientOrbitMap n i j ρ hρ q hfib).left =
        pointSection ((y ≫ q) ≫ quotientOrbitMap n i j ρ hρ q hfib) ≫
          matrixAction n (ρ.pointMatrix Z g) ≫ RelativeProjectiveSpace.map n Z.hom := by
    intro Z g y
    rw [hact, Category.assoc, Category.assoc, fac_quotientOrbitMap, pointSection_orbitMap,
      comp_orbitMap, orbitSection, orbitSection, map_mul, matrixAction_mul]
    simp only [Category.assoc]
  apply isMatrixEquivariant_of_universal
  have : EffectiveEpi (G.X ◁ q).left := Dynamic.flagQuotient_effectiveEpi_whiskerLeft G q G.X
  apply (cancel_epi (G.X ◁ q).left).mp
  have hL : (G.X ◁ q).left ≫ (a.hom ≫ quotientOrbitMap n i j ρ hρ q hfib).left =
      (a.act (fst G.X G.X) (snd G.X G.X ≫ q) ≫ quotientOrbitMap n i j ρ hρ q hfib).left := by
    rw [← Over.comp_left, SchemeAction.act, ← lift_whiskerLeft, lift_fst_snd,
      Category.id_comp, Category.assoc]
  have hR := pointSection_matrixAction_naturality ρ (G.X ◁ q) (fst G.X Q)
    (snd G.X Q ≫ quotientOrbitMap n i j ρ hρ q hfib)
  rw [whiskerLeft_fst, whiskerLeft_snd_assoc] at hR
  rw [hL, hR, ← Category.assoc (snd G.X G.X) q, hlift]

/-- The descended orbit map is a monomorphism of schemes. -/
theorem mono_quotientOrbitMap [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom) :
    Mono (quotientOrbitMap n i j ρ hρ q hfib).left := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ lineOrbitMap n j ρ = h ≫ lineOrbitMap n j ρ ↔
        relation (HomogeneousQuotientFromEmbedding.arrowSpace i)
          (HomogeneousQuotientFromEmbedding.source i)
          (HomogeneousQuotientFromEmbedding.target i) T ⟨g⟩ ⟨h⟩ := fun T g h =>
    (basisSection_orbitMap_fibers n i j ρ hρ T g h).trans
      (HomogeneousQuotientFromEmbedding.relation_iff i T g h).symm
  obtain ⟨Q', q', e, hqe, he, hsm, hsurj, hfib'⟩ :=
    exists_scheme_quotient_of_map_kernel
      (HomogeneousQuotientFromEmbedding.isEquivalenceRelation i)
      (HomogeneousQuotientFromEmbedding.hasSmoothProjections i hH)
      (inferInstance : LocallyOfFiniteType G.X.hom) _ _ hker
  have : Mono e.left := he
  have : Smooth q'.left := hsm
  have : Surjective q'.left := hsurj
  have : IsSeparated Q'.hom := by
    rw [← Over.w e]
    infer_instance
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : QuasiCompact (q'.left ≫ Q'.hom) := by
    rw [Over.w q']
    infer_instance
  have : QuasiCompact q'.left := QuasiCompact.of_comp q'.left Q'.hom
  have hfibs : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g ≫ q' = h ≫ q' := fun T g h =>
    (hfib T g h).trans
      ((HomogeneousQuotientFromEmbedding.relation_iff i T g h).symm.trans (hfib' T g h).symm)
  let c := HomogeneousQuotientComparison.iso q q' hfibs
  have hφ : quotientOrbitMap n i j ρ hρ q hfib = c.hom ≫ e := by
    symm
    apply HomogeneousQuotientComparison.desc_unique
    rw [HomogeneousQuotientComparison.comp_iso_hom_assoc, hqe]
  have : IsIso c.hom.left := inferInstanceAs (IsIso ((Over.forget _).map c.hom))
  rw [hφ, Over.comp_left]
  infer_instance

/-- For a proper quotient the descended orbit map is a closed immersion. -/
theorem isClosedImmersion_quotientOrbitMap [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom) [IsProper Q.hom] :
    IsClosedImmersion (quotientOrbitMap n i j ρ hρ q hfib).left := by
  have := mono_quotientOrbitMap n i j ρ hρ q hfib hi hH
  have : IsProper ((quotientOrbitMap n i j ρ hρ q hfib).left ≫
      (ambient n (CommRingCat.of k)).hom) := by
    rw [Over.w]
    infer_instance
  have : IsProper (quotientOrbitMap n i j ρ hρ q hfib).left :=
    IsProper.of_comp _ (ambient n (CommRingCat.of k)).hom
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end Quotient

end Langlands.GroupScheme.ProjectiveOrbit
