import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverStatement
import Langlands.GroupScheme.Absolute.BorelProperQuotientStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.FlagDualLineNeighbourhood
import Langlands.GroupScheme.FlagCoreDualLine
import Langlands.GroupScheme.SpanningLineStabilizerStatement
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.HomConjugacy

/-! # Reduction of invariant affine neighbourhoods to the dual-line core -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section Translation

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Right translation of a group scheme by a base point. -/
def rightTranslation (g : Over.mk (𝟙 S) ⟶ G.X) : G.X ⟶ G.X :=
  𝟙 G.X * G.constantPoint g G.X

/-- On every test, right translation multiplies on the right by the constant point. -/
theorem comp_rightTranslation (g : Over.mk (𝟙 S) ⟶ G.X) {T : Over S} (x : T ⟶ G.X) :
    x ≫ G.rightTranslation g = x * G.constantPoint g T := by
  rw [rightTranslation, MonObj.comp_mul, Category.comp_id, G.constantPoint_naturality]

theorem rightTranslation_comp_rightTranslation (g h : Over.mk (𝟙 S) ⟶ G.X) :
    G.rightTranslation g ≫ G.rightTranslation h = G.rightTranslation (g * h) := by
  rw [comp_rightTranslation, rightTranslation, rightTranslation, mul_assoc,
    ← constantPointHom_apply, ← constantPointHom_apply, ← constantPointHom_apply, map_mul]

theorem rightTranslation_one : G.rightTranslation 1 = 𝟙 G.X := by
  rw [rightTranslation, ← constantPointHom_apply, map_one, mul_one]

/-- Right translation by a base point as an automorphism of the underlying scheme. -/
@[simps]
def rightTranslationIso (g : Over.mk (𝟙 S) ⟶ G.X) : G.X ≅ G.X where
  hom := G.rightTranslation g
  inv := G.rightTranslation g⁻¹
  hom_inv_id := by
    rw [rightTranslation_comp_rightTranslation, mul_inv_cancel, rightTranslation_one]
  inv_hom_id := by
    rw [rightTranslation_comp_rightTranslation, inv_mul_cancel, rightTranslation_one]

variable {G} {B₀ B : GroupScheme S}

/-- If `b₀` conjugated by `g` is `b` up to isomorphism, a point lies in the range of `b` exactly
when its conjugate by `g⁻¹` lies in the range of `b₀`. -/
theorem mem_range_iff_conj_mem_range (b₀ : B₀ ⟶ G) (b : B ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X) (φ : B₀ ≅ B)
    (hg : b₀ ≫ (G.innerIso g).hom = φ.hom ≫ b) {T : Over S} (x : T ⟶ G.X) :
    x ∈ (SubgroupFunctor.range b).carrier T ↔
      (G.constantPoint g T)⁻¹ * x * G.constantPoint g T ∈
        (SubgroupFunctor.range b₀).carrier T := by
  have key : ∀ z : T ⟶ B₀.X, (z ≫ φ.hom.hom.hom) ≫ b.hom.hom =
      G.constantPoint g T * (z ≫ b₀.hom.hom) * (G.constantPoint g T)⁻¹ := by
    intro z
    have h := congrArg (fun f : B₀ ⟶ G => z ≫ f.hom.hom) hg
    simp only [Grp.comp_hom_hom] at h
    rw [Category.assoc, ← h, ← Category.assoc, comp_innerIso_hom]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ φ.inv.hom.hom, ?_⟩
    have hy : (y ≫ φ.inv.hom.hom) ≫ φ.hom.hom.hom = y := by
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id]
      rfl
    have := key (y ≫ φ.inv.hom.hom)
    rw [hy] at this
    rw [this]
    group
  · intro hx
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨w ≫ φ.hom.hom.hom, ?_⟩
    rw [key, hw]
    group

end Translation

section Properness

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G B : GroupScheme (Spec (CommRingCat.of k))}
variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Every flat quotient model of an arbitrary Borel subgroup is proper, assuming that some Borel
subgroup has proper smooth quotient models and that Borel subgroups are conjugate. -/
theorem IsBorelSubgroup.isProper_quotient_of_conjugacy
    (hproper : SomeBorelQuotientProperStatement.{u}) (hconj : BorelConjugacyStatement.{u})
    {b : B ⟶ G} (hb : IsBorelSubgroup b)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (Z : Over (Spec (CommRingCat.of k))) (g h : Z ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Z) :
    IsProper Q.hom := by
  obtain ⟨B₀, b₀, hb₀, hQ₀⟩ := hproper k G inferInstance
  obtain ⟨g, φ, hg⟩ := (hconj k G).2 B₀ B b₀ b hb₀ hb
  obtain ⟨Q₀, q₀, hsep, hlft, hqc, hsm, hsurj, hqqc, hfib₀⟩ :=
    smoothSubgroupQuotientExistence k G B₀ b₀ hb₀.isClosedSubgroup hb₀.smooth
  have hP₀ : IsProper Q₀.hom := hQ₀ Q₀ q₀ hsep hlft hqc hsm hsurj hqqc hfib₀
  have : Smooth q₀.left := hsm
  have : Surjective q₀.left := hsurj
  have : QuasiCompact q₀.left := hqqc
  let r : G.X ⟶ Q₀ := G.rightTranslation g ≫ q₀
  have : IsIso (G.rightTranslation g).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (G.rightTranslationIso g).hom))
  have : Flat r.left := by
    rw [Over.comp_left]
    infer_instance
  have : Surjective r.left := by
    rw [Over.comp_left]
    infer_instance
  have : QuasiCompact r.left := by
    rw [Over.comp_left]
    infer_instance
  have hfibs : ∀ (Z : Over (Spec (CommRingCat.of k))) (x y : Z ⟶ G.X),
      x ≫ q = y ≫ q ↔ x ≫ r = y ≫ r := by
    intro Z x y
    rw [hfib, ← Category.assoc, ← Category.assoc, comp_rightTranslation, comp_rightTranslation,
      hfib₀, mem_range_iff_conj_mem_range b₀ b g φ hg]
    constructor <;> intro h <;> convert h using 1 <;> group
  let e := HomogeneousQuotientComparison.iso q r hfibs
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  rw [← Over.w e.hom]
  infer_instance

end Properness

section Representation

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- A closed subgroup is the all-test stabilizer of a coordinate line in a representation whose
rational orbit through the distinguished basis vector spans, assuming the spanning statement. -/
theorem exists_spanning_line_stabilizer (hspan : SpanningLineStabilizerStatement.{u})
    (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      (∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
        x ∈ (SubgroupFunctor.range i).carrier Z ↔
          ∃ c : Γ(Z.left, ⊤)ˣ,
            (ρ.pointMatrix Z x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *ᵥ
                Pi.single j 1 =
              (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) :
                Fin (n + 1) → Γ(Z.left, ⊤))) ∧
      Submodule.span k (Set.range fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
          (ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
            (Pi.single j 1 : Fin (n + 1) → k)) = ⊤ := by
  obtain ⟨n, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G H i hi
  obtain ⟨n', j', ρ', h₁, h₂⟩ := hspan k G n j ρ
  exact ⟨n', j', ρ', fun Z x => (hρ Z x).trans (h₁ Z x).symm, h₂⟩

end Representation

/-- The invariant affine neighbourhood statement follows from the dual-line core, the spanning
line-stabilizer statement, properness of the quotients by some Borel subgroup, and Borel
conjugacy. -/
theorem flagInvariantAffineOpenCover_of_prerequisites
    (hcore : FlagCoreDualLineStatement.{u})
    (hspan : SpanningLineStabilizerStatement.{u})
    (hproper : SomeBorelQuotientProperStatement.{u})
    (hconj : BorelConjugacyStatement.{u}) :
    FlagInvariantAffineOpenCoverStatement.{u} := by
  intro k _ _ G _ _ _ T t ht U i hi hUs hUc hUu hthrough B b hb Q q hsep hlft hqc hflat hsurj
    hqqc hfib a hact x
  have : Flat q.left := hflat
  have : Surjective q.left := hsurj
  have : QuasiCompact q.left := hqqc
  obtain ⟨n, j, ρ, hρ, hρspan⟩ := exists_spanning_line_stabilizer hspan b hb.isClosedSubgroup
  have : IsProper Q.hom := hb.isProper_quotient_of_conjugacy hproper hconj q hfib
  exact exists_invariantAffineOpen_of_dualLines b hb.isClosedSubgroup hb.smooth i hUs n j ρ hρ
    q hfib a hact (hcore k G T t ht U i hthrough B b hb n j ρ hρ hρspan) x

end Langlands.GroupScheme
