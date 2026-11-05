import Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerProof
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.ClosedOrbitProof
import Langlands.GroupScheme.ElementaryOrbitLimit
import Langlands.GroupScheme.ProperPseudoComplete
import Langlands.GroupScheme.StabilizerClosedSubgroup

/-! # Proper orbits with a cocharacter-fixed point and solvable stabilizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SchemeAction

variable {k : Type u} [Field k]
    {X : Over (Spec (CommRingCat.of k))}

/-- An action of the multiplicative group on a proper scheme with a rational point
has an all-test fixed rational point. -/
theorem exists_isFixed_of_gm_of_isProper
    (a : SchemeAction (Gm (Spec (CommRingCat.of k))).toGrp X)
    [IsProper X.hom] (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    ∃ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y := by
  refine OrbitLimit.exists_isFixed_of_gm (Iso.refl _) a
    (isPseudoComplete_of_isProper X) (𝟙 _) (a.orbitMap x) ?_
  intro T h v
  rw [a.comp_orbitMap, a.comp_orbitMap, Grp.id_hom_hom, Category.comp_id,
    a.act_mul]

end SchemeAction

namespace Dynamic

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual proper homogeneous scheme with an all-test cocharacter-fixed point,
its solvable closed stabilizer, and a factorization of the supplied cocharacter. -/
structure CocharacterFixedOrbitData
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) where
  orbit : Over (Spec (CommRingCat.of k))
  action : SchemeAction G orbit
  point : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ orbit
  proper : IsProper orbit.hom
  reduced : IsReduced orbit.left
  transitive : ∀ z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ orbit,
    ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, action.act g point = z
  fixed : (action.restrict χ).IsFixed point
  stabilizer : GroupScheme (Spec (CommRingCat.of k))
  inclusion : stabilizer ⟶ G
  isClosedSubgroup : IsClosedSubgroup inclusion
  solvable : IsSolvableGroupScheme stabilizer
  stabilizer_points : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X),
    g ∈ (SubgroupFunctor.range inclusion).carrier T ↔
      action.act g (toUnit T ≫ point) = toUnit T ≫ point
  cocharacter : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ stabilizer
  cocharacter_comp : cocharacter ≫ inclusion = χ

variable [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- The closed orbit in the proper general-linear flag witness has a cocharacter-fixed
point, and its actual closed stabilizer is solvable and contains the cocharacter. -/
theorem nonempty_cocharacterFixedOrbitData
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Nonempty (CocharacterFixedOrbitData χ) := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨X, a, hXp, hXne, hsolv⟩ := generalLinearSolvableStabilizer k N
  have := hXp
  obtain ⟨O, j, b, x₀, hOred, hj, -, -, hjb, htrans⟩ :=
    closedOrbit k G X hXne (a.restrict ρ)
  have := hj
  have hOp : IsProper O.hom := by
    rw [← Over.w j]
    infer_instance
  have := hOp
  obtain ⟨y, hy⟩ := (b.restrict χ).exists_isFixed_of_gm_of_isProper x₀
  obtain ⟨S, iS, hiS, hS⟩ := b.exists_isClosedSubgroup_stabilizer y
  have hSsolv : IsSolvableGroupScheme S := by
    refine hsolv (y ≫ j) S (iS ≫ ρ) ?_ ?_
    · have h₁ : IsClosedImmersion iS.hom.hom.left := hiS
      have h₂ : IsClosedImmersion ρ.hom.hom.left := hρ
      show IsClosedImmersion (iS ≫ ρ).hom.hom.left
      simp only [Grp.comp_hom_hom, Over.comp_left]
      infer_instance
    · intro T c h
      rw [toUnit_unique c (toUnit T)]
      have hmem : h ≫ iS.hom.hom ∈ (SubgroupFunctor.range iS).carrier T :=
        SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩
      rw [hS] at hmem
      calc (a.restrict (iS ≫ ρ)).act h (toUnit T ≫ y ≫ j)
          = (a.restrict ρ).act (h ≫ iS.hom.hom) ((toUnit T ≫ y) ≫ j) := by
            simp only [SchemeAction.restrict_act, Grp.comp_hom_hom, Category.assoc]
        _ = b.act (h ≫ iS.hom.hom) (toUnit T ≫ y) ≫ j := (hjb _ _ _).symm
        _ = toUnit T ≫ y ≫ j := by rw [hmem, Category.assoc]
  have hχS : SubgroupFunctor.range χ ≤ SubgroupFunctor.range iS := by
    intro T g hg
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    rw [hS]
    simpa only [SchemeAction.restrict_act] using hy T (toUnit T) h
  have : IsClosedImmersion iS.hom.hom.left := hiS
  have : Mono iS.hom.hom := Over.mono_of_mono_left _
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp
    (hχS _ (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩))
  have : IsMonHom f := {
    one_hom := by
      apply (cancel_mono iS.hom.hom).mp
      rw [Category.assoc, hf, IsMonHom.one_hom, IsMonHom.one_hom]
    mul_hom := by
      apply (cancel_mono iS.hom.hom).mp
      rw [Category.assoc, hf, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
        tensorHom_comp_tensorHom_assoc, hf]
  }
  let χS := Grp.homMk f
  have hχScomp : χS ≫ iS = χ := Grp.hom_ext _ _ hf
  have htrans' : ∀ z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O,
      ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, b.act g y = z := by
    intro z
    obtain ⟨g₀, hg₀⟩ := htrans y
    obtain ⟨g₁, hg₁⟩ := htrans z
    refine ⟨g₁ * g₀⁻¹, ?_⟩
    rw [← hg₀, ← hg₁, ← b.act_mul, inv_mul_cancel_right]
  exact ⟨⟨O, b, y, hOp, hOred, htrans', hy, S, iS, hiS, hSsolv, hS, χS, hχScomp⟩⟩

/-- Choose the proper orbit and its actual solvable stabilizer, preserving the
specified cocharacter and its factorization. -/
def cocharacterFixedOrbitData
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    CocharacterFixedOrbitData χ :=
  Classical.choice (nonempty_cocharacterFixedOrbitData χ)

end Dynamic

end Langlands.GroupScheme
