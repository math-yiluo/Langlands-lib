import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Rational points of `GL_N` and of its block subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

open Langlands.GeneralLinear (BlockShape)

section RingEquiv

variable {n : Type} [Fintype n] [DecidableEq n] {A A' : Type u} [CommRing A] [CommRing A']

/-- Invertible matrices transported along a ring isomorphism of their entries. -/
def glRingEquiv (φ : A ≃+* A') : GL n A ≃* GL n A' :=
  Units.mapEquiv φ.mapMatrix.toMulEquiv

theorem glRingEquiv_apply (φ : A ≃+* A') (g : GL n A) (i j : n) :
    (glRingEquiv φ g : Matrix n n A') i j = φ ((g : Matrix n n A) i j) :=
  rfl

theorem glRingEquiv_eq_map (φ : A ≃+* A') (g : GL n A) :
    glRingEquiv φ g = Matrix.GeneralLinearGroup.map φ.toRingHom g :=
  Units.ext rfl

theorem glRingEquiv_symm_apply_apply (φ : A ≃+* A') (g : GL n A) :
    glRingEquiv φ.symm (glRingEquiv φ g) = g := by
  apply Units.ext
  ext i j
  simp only [glRingEquiv_apply, RingEquiv.symm_apply_apply]

variable (e : n → ℤ)

theorem glRingEquiv_mem_blockParabolicSubgroup_iff (φ : A ≃+* A') {g : GL n A} :
    glRingEquiv φ g ∈ blockParabolicSubgroup A' e ↔ g ∈ blockParabolicSubgroup A e := by
  constructor
  · intro h
    have h' := map_mem_blockParabolicSubgroup e φ.symm.toRingHom h
    rwa [← glRingEquiv_eq_map, glRingEquiv_symm_apply_apply] at h'
  · intro h
    rw [glRingEquiv_eq_map]
    exact map_mem_blockParabolicSubgroup e φ.toRingHom h

theorem glRingEquiv_mem_blockLeviSubgroup_iff (φ : A ≃+* A') {g : GL n A} :
    glRingEquiv φ g ∈ blockLeviSubgroup A' e ↔ g ∈ blockLeviSubgroup A e := by
  constructor
  · intro h
    have h' := map_mem_blockLeviSubgroup e φ.symm.toRingHom h
    rwa [← glRingEquiv_eq_map, glRingEquiv_symm_apply_apply] at h'
  · intro h
    rw [glRingEquiv_eq_map]
    exact map_mem_blockLeviSubgroup e φ.toRingHom h

theorem glRingEquiv_mem_blockUnipotentSubgroup_iff (φ : A ≃+* A') {g : GL n A} :
    glRingEquiv φ g ∈ blockUnipotentSubgroup A' e ↔ g ∈ blockUnipotentSubgroup A e := by
  constructor
  · intro h
    have h' := map_mem_blockUnipotentSubgroup e φ.symm.toRingHom h
    rwa [← glRingEquiv_eq_map, glRingEquiv_symm_apply_apply] at h'
  · intro h
    rw [glRingEquiv_eq_map]
    exact map_mem_blockUnipotentSubgroup e φ.toRingHom h

/-- Taking the block diagonal part commutes with a ring isomorphism of the entries. -/
theorem glRingEquiv_blockLeviProjection (φ : A ≃+* A') (g : blockParabolicSubgroup A e) :
    glRingEquiv φ (blockLeviProjection A e g) =
      blockLeviProjection A' e
        ⟨glRingEquiv φ g, (glRingEquiv_mem_blockParabolicSubgroup_iff e φ).2 g.2⟩ := by
  apply Units.ext
  ext i j
  rw [glRingEquiv_apply, coe_blockLeviProjection, coe_blockLeviProjection, blockDiagonalPart_apply,
    blockDiagonalPart_apply]
  split_ifs
  · rfl
  · exact map_zero φ

end RingEquiv

section BlockShape

variable {N : ℕ} (B : BlockShape N) {A A' : Type u} [CommRing A] [CommRing A']

theorem glRingEquiv_mem_parabolic_iff (φ : A ≃+* A') {g : Langlands.GeneralLinear N A} :
    glRingEquiv φ g ∈ B.parabolic A' ↔ g ∈ B.parabolic A := by
  rw [← blockParabolicSubgroup_blockShapeWeight, ← blockParabolicSubgroup_blockShapeWeight]
  exact glRingEquiv_mem_blockParabolicSubgroup_iff _ φ

theorem glRingEquiv_mem_leviSubgroup_iff (φ : A ≃+* A') {g : Langlands.GeneralLinear N A} :
    glRingEquiv φ g ∈ B.leviSubgroup A' ↔ g ∈ B.leviSubgroup A := by
  rw [← blockLeviSubgroup_blockShapeWeight, ← blockLeviSubgroup_blockShapeWeight]
  exact glRingEquiv_mem_blockLeviSubgroup_iff _ φ

theorem glRingEquiv_mem_unipotentSubgroup_iff (φ : A ≃+* A') {g : Langlands.GeneralLinear N A} :
    glRingEquiv φ g ∈ B.unipotentSubgroup A' ↔ g ∈ B.unipotentSubgroup A := by
  rw [← blockUnipotentSubgroup_blockShapeWeight, ← blockUnipotentSubgroup_blockShapeWeight]
  exact glRingEquiv_mem_blockUnipotentSubgroup_iff _ φ

/-- The Library's Levi part `B.leviEmbedding ∘ B.leviProjection` commutes with a ring isomorphism
of the entries. -/
theorem glRingEquiv_leviEmbedding_leviProjection (φ : A ≃+* A') (g : B.parabolic A) :
    glRingEquiv φ (B.leviEmbedding A (B.leviProjection A g)) =
      B.leviEmbedding A' (B.leviProjection A'
        ⟨glRingEquiv φ g, (glRingEquiv_mem_parabolic_iff B φ).2 g.2⟩) := by
  have hA := leviEmbedding_leviProjection B (A := A)
    ⟨g, (blockParabolicSubgroup_blockShapeWeight B A).symm ▸ g.2⟩
  have hA' := leviEmbedding_leviProjection B (A := A')
    ⟨glRingEquiv φ g, (blockParabolicSubgroup_blockShapeWeight B A').symm ▸
      (glRingEquiv_mem_parabolic_iff B φ).2 g.2⟩
  have e1 : MulEquiv.subgroupCongr (blockParabolicSubgroup_blockShapeWeight B A)
      ⟨g, (blockParabolicSubgroup_blockShapeWeight B A).symm ▸ g.2⟩ = g := Subtype.ext rfl
  have e2 : MulEquiv.subgroupCongr (blockParabolicSubgroup_blockShapeWeight B A')
      ⟨glRingEquiv φ g, (blockParabolicSubgroup_blockShapeWeight B A').symm ▸
        (glRingEquiv_mem_parabolic_iff B φ).2 g.2⟩ =
        ⟨glRingEquiv φ g, (glRingEquiv_mem_parabolic_iff B φ).2 g.2⟩ := Subtype.ext rfl
  rw [e1] at hA
  rw [e2] at hA'
  rw [hA, hA', glRingEquiv_blockLeviProjection]

end BlockShape

section RationalPoints

variable (N : ℕ) (R : CommRingCat.{u})

/-- The global sections of `Spec R`, identified with `R`. -/
abbrev globalSectionsEquiv : Γ((Over.mk (𝟙 (Spec R))).left, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- The rational points of `GL_N` over `Spec R` are the Library's `Langlands.GeneralLinear N R`:
the matrix of a point, with entries moved from `Γ(Spec R, ⊤)` to `R`. -/
def rationalPointsEquiv :
    (Over.mk (𝟙 (Spec R)) ⟶ (groupScheme (Fin N) R).X) ≃* Langlands.GeneralLinear N R :=
  (pointsEquiv (Fin N) R (Over.mk (𝟙 (Spec R)))).trans (glRingEquiv (globalSectionsEquiv R))

variable {N R}

theorem rationalPointsEquiv_apply_apply (x : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme (Fin N) R).X)
    (i j : Fin N) :
    (rationalPointsEquiv N R x : Matrix (Fin N) (Fin N) R) i j =
      (Scheme.ΓSpecIso R).hom (x.left.appTop (entrySection (Fin N) R i j)) := by
  change globalSectionsEquiv R (pointsEquiv (Fin N) R _ x i j) = _
  rw [pointsEquiv_apply_apply]
  rfl

variable (B : BlockShape N)

/-- Rational points of `P(λ_B)` are the matrices of the Library's block parabolic. -/
theorem mem_parabolic_blockShapeCocharacter_iff
    (x : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme (Fin N) R).X) :
    x ∈ (Dynamic.parabolic (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R))) ↔
      rationalPointsEquiv N R x ∈ B.parabolic R := by
  rw [parabolic_blockShapeCocharacter]
  exact (glRingEquiv_mem_parabolic_iff B (globalSectionsEquiv R)).symm

/-- Rational points of `Z(λ_B)` are the matrices of the Library's block Levi subgroup. -/
theorem mem_centralizer_blockShapeCocharacter_iff
    (x : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme (Fin N) R).X) :
    x ∈ (Dynamic.centralizer (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R))) ↔
      rationalPointsEquiv N R x ∈ B.leviSubgroup R := by
  rw [centralizer_blockShapeCocharacter]
  exact (glRingEquiv_mem_leviSubgroup_iff B (globalSectionsEquiv R)).symm

/-- Rational points of `U(λ_B)` are the matrices of the Library's block unipotent subgroup. -/
theorem mem_unipotent_blockShapeCocharacter_iff
    (x : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme (Fin N) R).X) :
    x ∈ (Dynamic.unipotent (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R))) ↔
      rationalPointsEquiv N R x ∈ B.unipotentSubgroup R := by
  rw [unipotent_blockShapeCocharacter]
  exact (glRingEquiv_mem_unipotentSubgroup_iff B (globalSectionsEquiv R)).symm

theorem map_parabolic_blockShapeCocharacter :
    ((Dynamic.parabolic (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))).map
      (rationalPointsEquiv N R).toMonoidHom = B.parabolic R := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_parabolic_blockShapeCocharacter_iff, MulEquiv.apply_symm_apply]

theorem map_centralizer_blockShapeCocharacter :
    ((Dynamic.centralizer (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))).map
      (rationalPointsEquiv N R).toMonoidHom = B.leviSubgroup R := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_centralizer_blockShapeCocharacter_iff, MulEquiv.apply_symm_apply]

theorem map_unipotent_blockShapeCocharacter :
    ((Dynamic.unipotent (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))).map
      (rationalPointsEquiv N R).toMonoidHom = B.unipotentSubgroup R := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_unipotent_blockShapeCocharacter_iff, MulEquiv.apply_symm_apply]

/-- The rational points of `P(λ_B)`, as the Library's block parabolic `B.parabolic R`. -/
def rationalParabolicEquiv :
    (Dynamic.parabolic (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R))) ≃*
      B.parabolic R :=
  ((rationalPointsEquiv N R).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_parabolic_blockShapeCocharacter B))

/-- The rational points of `Z(λ_B)`, as the Library's block Levi subgroup `B.leviSubgroup R`. -/
def rationalLeviEquiv :
    (Dynamic.centralizer (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R))) ≃*
      B.leviSubgroup R :=
  ((rationalPointsEquiv N R).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_centralizer_blockShapeCocharacter B))

/-- The rational points of `U(λ_B)`, as the Library's block unipotent subgroup
`B.unipotentSubgroup R`. -/
def rationalUnipotentEquiv :
    (Dynamic.unipotent (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R))) ≃*
      B.unipotentSubgroup R :=
  ((rationalPointsEquiv N R).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_unipotent_blockShapeCocharacter B))

@[simp] theorem rationalParabolicEquiv_coe
    (g : (Dynamic.parabolic (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))) :
    (rationalParabolicEquiv B g : Langlands.GeneralLinear N R) = rationalPointsEquiv N R g :=
  rfl

@[simp] theorem rationalLeviEquiv_coe
    (g : (Dynamic.centralizer (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))) :
    (rationalLeviEquiv B g : Langlands.GeneralLinear N R) = rationalPointsEquiv N R g :=
  rfl

@[simp] theorem rationalUnipotentEquiv_coe
    (g : (Dynamic.unipotent (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))) :
    (rationalUnipotentEquiv B g : Langlands.GeneralLinear N R) = rationalPointsEquiv N R g :=
  rfl

/-- The limit at zero of a rational point of `P(λ_B)` is the Library's Levi part
`B.leviEmbedding (B.leviProjection g)` of its matrix. -/
theorem rationalPointsEquiv_limit
    (g : (Dynamic.parabolic (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))) :
    rationalPointsEquiv N R (Dynamic.limit (blockShapeCocharacter B R) g) =
      B.leviEmbedding R (B.leviProjection R (rationalParabolicEquiv B g)) := by
  obtain ⟨hg, hl⟩ := hasLimit_blockShapeCocharacter_iff.1 (Dynamic.hasLimit_limit _ g)
  change glRingEquiv (globalSectionsEquiv R) (pointsEquiv (Fin N) R _ _) = _
  rw [hl, glRingEquiv_leviEmbedding_leviProjection]
  rfl


/-- The limit homomorphism `P(λ_B)(R) →* Z(λ_B)(R)` is the Library's Levi projection
`B.leviProjection`, followed by the Library's isomorphism `B.leviEquiv` onto the block Levi
subgroup. -/
theorem rationalLeviEquiv_limitHom
    (g : (Dynamic.parabolic (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))) :
    rationalLeviEquiv B (Dynamic.limitHom (blockShapeCocharacter B R) _ g) =
      B.leviEquiv R (B.leviProjection R (rationalParabolicEquiv B g)) :=
  Subtype.ext (rationalPointsEquiv_limit B g)

/-- The section `Z(λ_B)(R) ≤ P(λ_B)(R)` of the limit homomorphism is the Library's inclusion
`B.leviAsParabolic` of the block Levi subgroup in the block parabolic. -/
theorem rationalParabolicEquiv_inclusion
    (z : (Dynamic.centralizer (blockShapeCocharacter B R)).carrier (Over.mk (𝟙 (Spec R)))) :
    rationalParabolicEquiv B
        (Subgroup.inclusion (Dynamic.centralizer_le_parabolic _ (Over.mk (𝟙 (Spec R)))) z) =
      B.leviAsParabolic R (rationalLeviEquiv B z) :=
  rfl

end RationalPoints

end Langlands.GroupScheme.GeneralLinear
