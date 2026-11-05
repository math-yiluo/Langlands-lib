import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentHeight
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Dynamic.OppositeCellContraction

/-! # Heights on opposite unipotent points bounded by a Chevalley line for the parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section LineCriterion

/-- The basis vector `e j` is an eigenvector of `M` with a unit eigenvalue exactly when it is
such an eigenvector of the image of `M` under a ring isomorphism. -/
theorem exists_mulVec_single_eq_smul_map_iff {A B : Type*} [CommRing A] [CommRing B]
    (φ : A ≃+* B) {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n A) (j : n) :
    (∃ u : Bˣ, M.map φ *ᵥ Pi.single j 1 = (u : B) • Pi.single j 1) ↔
      ∃ u : Aˣ, M *ᵥ Pi.single j 1 = (u : A) • Pi.single j 1 := by
  have key : ∀ u : Aˣ,
      (M.map φ *ᵥ Pi.single j 1 = ((Units.map φ.toMonoidHom u : Bˣ) : B) • Pi.single j 1 ↔
        M *ᵥ Pi.single j 1 = (u : A) • Pi.single j 1) := by
    intro u
    have hmap : M.map φ *ᵥ Pi.single j 1 = φ ∘ (M *ᵥ Pi.single j 1) := by
      funext i
      simp
    have hsmul : ((Units.map φ.toMonoidHom u : Bˣ) : B) • (Pi.single j 1 : n → B) =
        φ ∘ ((u : A) • (Pi.single j 1 : n → A)) := by
      funext i
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    rw [hmap, hsmul]
    exact (φ.injective.comp_left).eq_iff
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Units.map φ.symm.toMonoidHom v, (key _).1 ?_⟩
    convert hv using 3
    ext
    simp
  · rintro ⟨u, hu⟩
    exact ⟨_, (key u).2 hu⟩

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- `IsRationalLineStabilizer ρ j S` says that a rational point `x` of `G` lies in the subgroup
`S` of `G(k)` exactly when `ρ(x)` maps the basis vector `e j` to a unit multiple of itself, that
is, `S` is the stabilizer in `G(k)` of the line `k e j`. -/
def IsRationalLineStabilizer {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (j : n) (S : Subgroup (rationalPoints G)) : Prop :=
  ∀ x : rationalPoints G, x ∈ S ↔
    ∃ u : kˣ, (ρ.rationalMatrix x : Matrix n n k) *ᵥ Pi.single j 1 = (u : k) • Pi.single j 1

/-- A point of the stabilizer moves `e j` within its line. -/
theorem IsRationalLineStabilizer.exists_unit_of_mem {n : Type} [Fintype n] [DecidableEq n]
    {ρ : MatrixRepresentation G n} {j : n} {S : Subgroup (rationalPoints G)}
    (h : IsRationalLineStabilizer ρ j S) {x : rationalPoints G} (hx : x ∈ S) :
    ∃ u : kˣ, (ρ.rationalMatrix x : Matrix n n k) *ᵥ Pi.single j 1 = (u : k) • Pi.single j 1 :=
  (h x).1 hx

/-- A point fixing `e j` lies in the stabilizer. -/
theorem IsRationalLineStabilizer.mem_of_mulVec_eq {n : Type} [Fintype n] [DecidableEq n]
    {ρ : MatrixRepresentation G n} {j : n} {S : Subgroup (rationalPoints G)}
    (h : IsRationalLineStabilizer ρ j S) {x : rationalPoints G}
    (hx : (ρ.rationalMatrix x : Matrix n n k) *ᵥ Pi.single j 1 = Pi.single j 1) : x ∈ S :=
  (h x).2 ⟨1, by rw [hx, Units.val_one, one_smul]⟩

/-- **Rational line stabilizers.** For a closed subgroup `i : H → G` of an affine group of
finite type over a field `k`, there is a representation `ρ` of `G` and a basis vector `e j`
such that a rational point `x` of `G` lies in `H(k)` exactly when `ρ(x) e j ∈ kˣ e j`. -/
theorem exists_rationalMatrix_line_stabilizer (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (hc : IsClosedSubgroup i) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      IsRationalLineStabilizer ρ j (SubgroupFunctor.range i).rationalPoints := by
  obtain ⟨n, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G H i hc
  refine ⟨n, j, ρ, ?_⟩
  intro x
  rw [hρ (Over.mk (𝟙 _)) x]
  exact (exists_mulVec_single_eq_smul_map_iff
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv _ j).symm

end LineCriterion

section Parabolic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Rational points of a cocharacter lie in its dynamic parabolic subgroup. -/
theorem gmRationalPoint_comp_mem_parabolic (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (t : kˣ) : gmRationalPoint t ≫ χ.hom.hom ∈ (Dynamic.parabolic χ).rationalPoints := by
  have hr := Dynamic.range_comp_le_centralizer_comp χ (𝟙 _) (𝟙 _)
  simp only [Category.id_comp] at hr
  exact Dynamic.centralizer_le_parabolic χ _
    (hr _ (SubgroupFunctor.mem_range.mpr ⟨gmRationalPoint t, rfl⟩))

/-- **Chevalley line for a dynamic parabolic.** For a cocharacter `χ` of an affine group `G` of
finite type over a field, there is a representation `ρ` and a basis vector `e j` such that
`P(χ)(k)` is exactly the set of rational points `x` with `ρ(x) e j ∈ kˣ e j`. -/
theorem exists_parabolic_line [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      IsRationalLineStabilizer ρ j (Dynamic.parabolic χ).rationalPoints := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨n, j, ρ, hρ⟩ := exists_rationalMatrix_line_stabilizer G _
    (Dynamic.Affine.parabolicHom χ) (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
  refine ⟨n, j, ρ, ?_⟩
  intro x
  rw [← hρ x, (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2]

end Parabolic

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- **Heights on opposite unipotent points from the parabolic line.** Let `χ` be a cocharacter
of an affine group `G` of finite type over a non-archimedean local field `F`, and `ρ₀` a closed
representation of `G`. There are a representation `ρ` and a basis vector `e j` cutting out
`P(χ)(F)` as in `exists_parabolic_line`, together with `C > 0` and `D` such that the
`ρ₀`-height of every `x ∈ Ū(F) = U(χ⁻¹)(F)` is at most `C * max 1 ‖ρ(x) e j‖ ^ D`. -/
theorem exists_parabolic_line_rationalMatrixNorm_le [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N))
    (hρ₀ : IsClosedSubgroup ρ₀) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      IsRationalLineStabilizer ρ j (Dynamic.parabolic χ).rationalPoints ∧
      ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧
        ∀ x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).rationalPoints,
          rationalMatrixNorm F ρ₀ x ≤ C * max 1 (rationalVectorNorm F
            ((ρ.rationalMatrix x : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
              Pi.single j 1)) ^ D := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨n, j, ρ, hρ⟩ := exists_parabolic_line χ
  refine ⟨n, j, ρ, hρ, ?_⟩
  have hv : IsCocharacterEigenvector χ ρ (Pi.single j 1) := fun t => by
    obtain ⟨u, hu⟩ := hρ.exists_unit_of_mem (gmRationalPoint_comp_mem_parabolic χ t)
    exact ⟨u, hu⟩
  refine exists_rationalMatrixNorm_le_of_weightVector F χ ρ₀ hρ₀ ρ hv fun x hx hfx => ?_
  exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hx (hρ.mem_of_mulVec_eq hfx)

end LocalField

end Langlands.GroupScheme.MatrixRepresentation
