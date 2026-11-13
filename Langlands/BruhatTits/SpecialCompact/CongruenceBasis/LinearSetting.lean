import Langlands.BruhatTits.SpecialCompact.CongruenceBasis.GLCongruence
import Langlands.GroupScheme.Dynamic.TriangularCell
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Congruence subgroups pulled back along a closed embedding into `GL_N` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.SpecialCompact.CongruenceGL

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear Langlands.GroupScheme.Dynamic

variable {F : Type u} [Field F] {N : ℕ}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (ρ : G ⟶ groupScheme (Fin N) (CommRingCat.of F))

/-- The matrix in `GL_N(F)` of the image under `ρ` of a rational point of `G`. -/
def pointMatrix : rationalPoints G →* GL (Fin N) F :=
  (rationalPointsEquiv N (CommRingCat.of F)).toMonoidHom.comp (rationalPoints.map ρ)

theorem pointMatrix_apply (x : rationalPoints G) :
    pointMatrix ρ x = glRingEquiv (globalSectionsEquiv (CommRingCat.of F))
      (pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _)) (x ≫ ρ.hom.hom)) :=
  rfl

variable {R : Type*} [CommRing R] (f : R →+* F) (I : Ideal R)

/-- The preimage under `ρ` of the principal congruence subgroup of level `I`, whose integral
matrices over `R` are mapped to `GL_N(F)` by `f`. -/
def linearCongruence : Subgroup (rationalPoints G) :=
  ((kernel R I).map (Matrix.GeneralLinearGroup.map (n := Fin N) f)).comap (pointMatrix ρ)

theorem mem_linearCongruence {g : rationalPoints G} :
    g ∈ linearCongruence ρ f I ↔
      pointMatrix ρ g ∈ (kernel R I).map (Matrix.GeneralLinearGroup.map (n := Fin N) f) :=
  Iff.rfl

variable {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {e : Fin N → ℤ}

/-- The matrix of a cocharacter point is the diagonal matrix of the weights. -/
theorem pointMatrix_cocharacter
    (hχ : χ ≫ ρ = diagonalCocharacter (Fin N) (CommRingCat.of F) e) (t : Fˣ) :
    pointMatrix ρ (rationalPoints.map χ
        ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t)) =
      diagonalUnits F e t := by
  set s := (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t with hs
  have h1 : rationalPoints.map χ s ≫ ρ.hom.hom =
      s ≫ (diagonalCocharacter (Fin N) (CommRingCat.of F) e).hom.hom := by
    rw [← hχ, Grp.comp_hom_hom, rationalPoints.map_apply, Category.assoc]
  rw [pointMatrix_apply, h1, pointsEquiv_diagonalCocharacter, glRingEquiv_eq_map,
    map_diagonalUnits]
  have key : Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F))) s = t :=
    MulEquiv.apply_symm_apply _ t
  rw [← key]
  rfl

section Transport

variable {ρ}

theorem pointMatrix_mem_blockParabolicSubgroup_iff (x : rationalPoints G) :
    pointMatrix ρ x ∈ blockParabolicSubgroup F e ↔
      pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _)) (x ≫ ρ.hom.hom) ∈
        blockParabolicSubgroup Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤) e :=
  glRingEquiv_mem_blockParabolicSubgroup_iff e _

theorem pointMatrix_mem_blockLeviSubgroup_iff (x : rationalPoints G) :
    pointMatrix ρ x ∈ blockLeviSubgroup F e ↔
      pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _)) (x ≫ ρ.hom.hom) ∈
        blockLeviSubgroup Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤) e :=
  glRingEquiv_mem_blockLeviSubgroup_iff e _

theorem pointMatrix_mem_blockUnipotentSubgroup_iff (x : rationalPoints G) :
    pointMatrix ρ x ∈ blockUnipotentSubgroup F e ↔
      pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _)) (x ≫ ρ.hom.hom) ∈
        blockUnipotentSubgroup Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤) e :=
  glRingEquiv_mem_blockUnipotentSubgroup_iff e _

variable [IsClosedImmersion ρ.hom.hom.left]

theorem pointMatrix_mem_parabolic
    (hχ : χ ≫ ρ = diagonalCocharacter (Fin N) (CommRingCat.of F) e) {x : rationalPoints G}
    (hx : x ∈ (parabolic χ).carrier (Over.mk (𝟙 _))) :
    pointMatrix ρ x ∈ blockParabolicSubgroup F e :=
  (pointMatrix_mem_blockParabolicSubgroup_iff x).2 ((mem_parabolic_iff_of_diagonal hχ x).1 hx)

theorem pointMatrix_mem_opposite_unipotent
    (hχ : χ ≫ ρ = diagonalCocharacter (Fin N) (CommRingCat.of F) e) {x : rationalPoints G}
    (hx : x ∈ (unipotent (oppositeCocharacter χ)).carrier (Over.mk (𝟙 _))) :
    pointMatrix ρ x ∈ blockUnipotentSubgroup F (-e) :=
  (pointMatrix_mem_blockUnipotentSubgroup_iff x).2 ((mem_unipotent_iff_of_diagonal hχ x).1 hx)

omit [IsClosedImmersion ρ.hom.hom.left] in
theorem pointMatrix_mem_centralizer
    (hχ : χ ≫ ρ = diagonalCocharacter (Fin N) (CommRingCat.of F) e) {x : rationalPoints G}
    (hx : x ∈ (centralizer χ).carrier (Over.mk (𝟙 _))) :
    pointMatrix ρ x ∈ blockLeviSubgroup F e := by
  have h := centralizer_le_comap χ ρ (Over.mk (𝟙 _)) hx
  rw [SubgroupFunctor.mem_comap, hχ, centralizer_diagonalCocharacter] at h
  exact (pointMatrix_mem_blockLeviSubgroup_iff x).2 h

omit [IsClosedImmersion ρ.hom.hom.left] in
theorem pointMatrix_mem_unipotent
    (hχ : χ ≫ ρ = diagonalCocharacter (Fin N) (CommRingCat.of F) e) {x : rationalPoints G}
    (hx : x ∈ (unipotent χ).carrier (Over.mk (𝟙 _))) :
    pointMatrix ρ x ∈ blockUnipotentSubgroup F e := by
  have h := unipotent_le_comap χ ρ (Over.mk (𝟙 _)) hx
  rw [SubgroupFunctor.mem_comap, hχ, unipotent_diagonalCocharacter] at h
  exact (pointMatrix_mem_blockUnipotentSubgroup_iff x).2 h

end Transport

variable [IsClosedImmersion ρ.hom.hom.left]

/-- **Iwahori factorization of a linear congruence subgroup.** If `χ ≫ ρ` is diagonal and the
level `I` lies in the maximal ideal of the local ring `R`, every element of the pulled-back
congruence subgroup is an ordered product of elements of it lying in `U(χ⁻¹)`, `Z(χ)` and
`U(χ)`. -/
theorem exists_linearCongruence_triple [IsLocalRing R]
    (hχ : χ ≫ ρ = diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (hI : I ≤ IsLocalRing.maximalIdeal R) {g : rationalPoints G}
    (hg : g ∈ linearCongruence ρ f I) :
    ∃ a ∈ linearCongruence ρ f I ⊓ (unipotent (oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)),
      ∃ b ∈ linearCongruence ρ f I ⊓ (centralizer χ).carrier (Over.mk (𝟙 _)),
        ∃ c ∈ linearCongruence ρ f I ⊓ (unipotent χ).carrier (Over.mk (𝟙 _)),
          g = a * b * c := by
  have : IsSeparated G.X.hom := fieldSeparated F G
  obtain ⟨C, hC, hCg⟩ := hg
  have hunit : IsUnit (cellMinor e (pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _))
      (g ≫ ρ.hom.hom) : Matrix (Fin N) (Fin N)
        Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤))) := by
    have h1 : IsUnit (f (cellMinor e (C : Matrix (Fin N) (Fin N) R))) :=
      (isUnit_cellMinor_of_mem_kernel hI e hC).map f
    have h2 : (C : Matrix (Fin N) (Fin N) R).map f =
        (pointsEquiv (Fin N) (CommRingCat.of F) (Over.mk (𝟙 _)) (g ≫ ρ.hom.hom) :
          Matrix (Fin N) (Fin N) Γ((Over.mk (𝟙 (Spec (CommRingCat.of F)))).left, ⊤)).map
          (globalSectionsEquiv (CommRingCat.of F)).toRingHom :=
      congrArg (fun X : GL (Fin N) F => (X : Matrix (Fin N) (Fin N) F)) hCg
    rw [map_cellMinor, h2, ← map_cellMinor] at h1
    exact (isUnit_map_iff (globalSectionsEquiv (CommRingCat.of F)) _).1 h1
  obtain ⟨p, hp, hgp⟩ := exists_mem_parabolic_of_isUnit_cellMinor hχ g hunit
  set b := limit χ ⟨p, hp⟩ with hb_def
  have hbZ : b ∈ (centralizer χ).carrier (Over.mk (𝟙 _)) := limit_mem_centralizer χ ⟨p, hp⟩
  have hpb : p * b⁻¹ ∈ (unipotent χ).carrier (Over.mk (𝟙 _)) :=
    mul_inv_limit_mem_unipotent χ ⟨p, hp⟩
  have hbinvP : b⁻¹ ∈ (parabolic χ).carrier (Over.mk (𝟙 _)) :=
    centralizer_le_parabolic χ _ (((centralizer χ).carrier _).inv_mem hbZ)
  have hc : b⁻¹ * p ∈ (unipotent χ).carrier (Over.mk (𝟙 _)) := by
    have h := conj_mem_unipotent χ hbinvP hpb
    rwa [inv_inv, mul_assoc, inv_mul_cancel_right] at h
  have hga : g = g * p⁻¹ * b * (b⁻¹ * p) := by
    rw [mul_assoc (g * p⁻¹), mul_inv_cancel_left, inv_mul_cancel_right]
  have ha_mat : pointMatrix ρ (g * p⁻¹) ∈ blockUnipotentSubgroup F (-e) :=
    pointMatrix_mem_opposite_unipotent hχ hgp
  have hb_mat : pointMatrix ρ b ∈ blockLeviSubgroup F e := pointMatrix_mem_centralizer hχ hbZ
  have hc_mat : pointMatrix ρ (b⁻¹ * p) ∈ blockUnipotentSubgroup F e :=
    pointMatrix_mem_unipotent hχ hc
  obtain ⟨u, hu, d, hd, v, hv, hCuv⟩ := exists_kernel_blockTriple hI e hC
  have hprod : pointMatrix ρ (g * p⁻¹) * pointMatrix ρ b * pointMatrix ρ (b⁻¹ * p) =
      Matrix.GeneralLinearGroup.map f (u * d * v) := by
    rw [← map_mul, ← map_mul, ← hga, ← hCuv, hCg]
  obtain ⟨h1, h2, h3⟩ := blockTriple_eq_map e f hu.2 hd.2 hv.2 ha_mat hb_mat hc_mat hprod
  exact ⟨g * p⁻¹, ⟨⟨u, hu.1, h1.symm⟩, hgp⟩, b, ⟨⟨d, hd.1, h2.symm⟩, hbZ⟩, b⁻¹ * p,
    ⟨⟨v, hv.1, h3.symm⟩, hc⟩, hga⟩

/-- **Contraction of a linear congruence subgroup.** Conjugation by the cocharacter point
`χ(t)`, for a unit `t` of `F` coming from `R`, preserves the elements of the pulled-back
congruence subgroup lying in `P(χ)`. -/
theorem conj_mem_linearCongruence
    (hχ : χ ≫ ρ = diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (hf : Function.Injective f) (t : Fˣ) (r : R) (htr : (t : F) = f r)
    {g : rationalPoints G} (hg : g ∈ linearCongruence ρ f I)
    (hgP : g ∈ (parabolic χ).carrier (Over.mk (𝟙 _))) :
    rationalPoints.map χ ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t) * g *
        (rationalPoints.map χ ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm t))⁻¹ ∈
      linearCongruence ρ f I := by
  rw [mem_linearCongruence, map_mul, map_mul, map_inv, pointMatrix_cocharacter ρ hχ]
  obtain ⟨C, hC, hCg⟩ := hg
  rw [← hCg]
  refine diagonalUnits_conj_mem_map_kernel f hf e r t htr hC ?_
  rw [hCg]
  exact pointMatrix_mem_parabolic hχ hgP

end Langlands.BruhatTits.SpecialCompact.CongruenceGL
