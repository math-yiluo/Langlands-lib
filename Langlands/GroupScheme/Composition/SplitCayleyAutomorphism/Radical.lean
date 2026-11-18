import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.RadicalAlgebra
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Connected
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Smooth
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # The split Cayley automorphism group is connected reductive

The unipotent radical of the automorphism group scheme of Zorn's split Cayley algebra is trivial
over an algebraically closed field (`hasTrivialUnipotentRadical_of_isAlgClosed`); with smoothness
and connectedness this makes the automorphism group scheme connected reductive over every field
(`isConnectedReductive`).

The argument uses the seven-dimensional representation `quotRep` on the quotient of Zorn's
algebra by the line of the unit. A smooth connected unipotent normal subgroup `H` has a nonzero
fixed vector there; its preimage in Zorn's algebra is stable under all rational automorphisms by
normality, so contains `u₁, …, v₃` (`stableSubspace`). Every point of `H` then moves `u₁, …, v₃`
only by multiples of the unit, so is the identity (`unitRigidity`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

variable {K : Type u} [Field K]

/-! ### The quotient representation -/

section QuotRep

theorem mulVec_unit_of_mem {A : Type u} [CommRing A] {φ : K →+* A} {g : GL (Fin 8) A}
    (hg : g ∈ (CayleyDatum.split K).automorphismSubgroup φ) :
    (g : Matrix (Fin 8) (Fin 8) A) *ᵥ unit A = unit A :=
  ((mem_automorphismSubgroup_split_iff φ g).1 hg).1

/-- Automorphism matrices act on the quotient of `A⁸` by the line of the unit. -/
def quotHom {A : Type u} [CommRing A] (φ : K →+* A) :
    (CayleyDatum.split K).automorphismSubgroup φ →* GL (Fin 7) A where
  toFun g :=
    { val := quotMatrix ((g : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A)
      inv := quotMatrix (((g : GL (Fin 8) A)⁻¹ : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A)
      val_inv := by
        rw [← quotMatrix_mul (mulVec_unit_of_mem g.2), ← Units.val_mul, mul_inv_cancel,
          Units.val_one, quotMatrix_one]
      inv_val := by
        rw [← quotMatrix_mul (mulVec_unit_of_mem (inv_mem g.2)), ← Units.val_mul,
          inv_mul_cancel, Units.val_one, quotMatrix_one] }
  map_one' := Units.ext quotMatrix_one
  map_mul' g h := Units.ext (quotMatrix_mul (mulVec_unit_of_mem g.2) _)

@[simp] theorem quotHom_val {A : Type u} [CommRing A] (φ : K →+* A)
    (g : (CayleyDatum.split K).automorphismSubgroup φ) :
    ((quotHom φ g : GL (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      quotMatrix ((g : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A) :=
  rfl

variable (K) in
/-- The quotient representation on points of every test scheme. -/
def quotPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (CayleyDatum.split K).automorphismGroup.X) →*
      (T ⟶ (GeneralLinear.groupScheme (Fin 7) (CommRingCat.of K)).X) :=
  (GeneralLinear.pointsEquiv (Fin 7) _ T).symm.toMonoidHom.comp
    ((quotHom (scalarMap T)).comp (pointsEquiv K T).toMonoidHom)

theorem pointsEquiv_quotPoints {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (CayleyDatum.split K).automorphismGroup.X) :
    GeneralLinear.pointsEquiv (Fin 7) _ T (quotPoints K T x) =
      quotHom (scalarMap T) (pointsEquiv K T x) :=
  MulEquiv.apply_symm_apply _ _

theorem quotPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (CayleyDatum.split K).automorphismGroup.X) :
    quotPoints K T' (a ≫ x) = a ≫ quotPoints K T x := by
  apply (GeneralLinear.pointsEquiv (Fin 7) _ T').injective
  apply Units.ext
  have hmap : ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (y : GL (Fin 7) A),
      ((Matrix.GeneralLinearGroup.map f y : GL (Fin 7) B) : Matrix (Fin 7) (Fin 7) B) =
        (y : Matrix (Fin 7) (Fin 7) A).map f := fun _ _ => rfl
  rw [GeneralLinear.pointsEquiv_naturality, pointsEquiv_quotPoints, pointsEquiv_quotPoints,
    hmap, quotHom_val, quotHom_val, pointsEquiv_naturality, quotMatrix_map]

variable (K) in
/-- The seven-dimensional representation of the automorphism group scheme on the quotient of
Zorn's algebra by the line of the unit. -/
def quotRep : MatrixRepresentation (CayleyDatum.split K).automorphismGroup (Fin 7) :=
  homOfPoints (quotPoints K) (fun {_ _} a x => quotPoints_naturality a x)

theorem pointsEquiv_quotRep {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (CayleyDatum.split K).automorphismGroup.X) :
    GeneralLinear.pointsEquiv (Fin 7) _ T (x ≫ (quotRep K).hom.hom) =
      quotHom (scalarMap T) (pointsEquiv K T x) := by
  rw [quotRep, comp_homOfPoints, pointsEquiv_quotPoints]

end QuotRep

/-! ### Rational points as points over every test scheme -/

section Constant

/-- Automorphism matrices over the base field stay automorphism matrices after every change of
coefficients. -/
theorem map_mem_automorphismSubgroup {A : Type u} [CommRing A] (f : K →+* A)
    {g : GL (Fin 8) K} (hg : g ∈ (CayleyDatum.split K).automorphismSubgroup (RingHom.id K)) :
    Matrix.GeneralLinearGroup.map f g ∈ (CayleyDatum.split K).automorphismSubgroup f := by
  rw [CayleyDatum.mem_automorphismSubgroup, CayleyDatum.isAutomorphismMatrix_iff] at hg ⊢
  obtain ⟨hu, hm⟩ := hg
  refine ⟨fun i => ?_, fun i j l => ?_⟩
  · have h := (CayleyDatum.split K).map_unitDefect (RingHom.id K) f
      ((g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) i
    rw [hu i, map_zero, RingHom.comp_id] at h
    exact h.symm
  · have h := (CayleyDatum.split K).map_multiplicationDefect (RingHom.id K) f
      ((g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) (Pi.single j 1) (Pi.single l 1) i
    rw [hm i j l, map_zero, RingHom.comp_id] at h
    have hs : ∀ m : Fin 8, (fun l' => f ((Pi.single m (1 : K) : Fin 8 → K) l')) =
        (Pi.single m 1 : Fin 8 → A) := by
      intro m
      funext l'
      by_cases hl : l' = m
      · subst hl
        simp
      · simp [hl]
    rw [hs, hs] at h
    exact h.symm

/-- The point of the automorphism group scheme over a test scheme given by a rational
automorphism matrix. -/
def constantPoint (T : Over (Spec (CommRingCat.of K)))
    (g : (CayleyDatum.split K).automorphismSubgroup (RingHom.id K)) :
    T ⟶ (CayleyDatum.split K).automorphismGroup.X :=
  (pointsEquiv K T).symm ⟨Matrix.GeneralLinearGroup.map (scalarMap T) g,
    map_mem_automorphismSubgroup (scalarMap T) g.2⟩

theorem pointsEquiv_constantPoint (T : Over (Spec (CommRingCat.of K)))
    (g : (CayleyDatum.split K).automorphismSubgroup (RingHom.id K)) :
    ((pointsEquiv K T (constantPoint T g) : GL (Fin 8) Γ(T.left, ⊤)) :
        Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤)) =
      ((g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K).map (scalarMap T) := by
  rw [constantPoint, MulEquiv.apply_symm_apply]
  rfl

/-- Normality makes the fixed vectors of the quotient representation of a normal subgroup stable
under rational automorphisms. -/
theorem quotMatrix_mulVec_mem_fixedSubmodule {H : GroupScheme (Spec (CommRingCat.of K))}
    (i : H ⟶ (CayleyDatum.split K).automorphismGroup)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (g : (CayleyDatum.split K).automorphismSubgroup (RingHom.id K))
    {v : Fin 7 → K} (hv : v ∈ MatrixRepresentation.fixedSubmodule (i ≫ quotRep K)) :
    quotMatrix ((g : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *ᵥ v ∈
      MatrixRepresentation.fixedSubmodule (i ≫ quotRep K) := by
  intro T h
  obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1
    (hN T (constantPoint T g)⁻¹ (h ≫ i.hom.hom) trivial
      (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
  have key := hv T h'
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_quotRep, hh'] at key
  simp only [map_mul, map_inv, inv_inv] at key
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_quotRep]
  have hg : (fun j => scalarMap T ((quotMatrix ((g : GL (Fin 8) K) :
      Matrix (Fin 8) (Fin 8) K) *ᵥ v) j)) =
      ((quotHom (scalarMap T) (pointsEquiv K T (constantPoint T g)) : GL (Fin 7) Γ(T.left, ⊤)) :
        Matrix (Fin 7) (Fin 7) Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j)) := by
    funext j
    rw [RingHom.map_mulVec, quotMatrix_map, quotHom_val, pointsEquiv_constantPoint,
      Function.comp_def]
  rw [hg]
  set G := quotHom (scalarMap T) (pointsEquiv K T (constantPoint T g))
  set M := quotHom (scalarMap T) (pointsEquiv K T (h ≫ i.hom.hom))
  have e1 : (M : Matrix (Fin 7) (Fin 7) Γ(T.left, ⊤)) *ᵥ
      ((G : Matrix (Fin 7) (Fin 7) Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j))) =
      (G : Matrix (Fin 7) (Fin 7) Γ(T.left, ⊤)) *ᵥ
        (((G⁻¹ * M * G : GL (Fin 7) Γ(T.left, ⊤)) : Matrix (Fin 7) (Fin 7) Γ(T.left, ⊤)) *ᵥ
          (fun j => scalarMap T (v j))) := by
    have hc : G * (G⁻¹ * M * G) = M * G := by group
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hc]
  rw [e1, key]

end Constant

/-! ### The unipotent radical -/

section Radical

theorem mem_automorphismSubgroup_id_iff {g : GL (Fin 8) K} :
    g ∈ (CayleyDatum.split K).automorphismSubgroup (RingHom.id K) ↔
      IsAutomorphism (g : Matrix (Fin 8) (Fin 8) K).mulVec :=
  mem_automorphismSubgroup_split_iff _ g

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, every smooth connected unipotent normal closed subgroup
of the split Cayley automorphism group scheme is trivial. -/
theorem hasTrivialUnipotentRadical_of_isAlgClosed :
    HasTrivialUnipotentRadical (CayleyDatum.split k).automorphismGroup := by
  intro H i _ _ _ hU hN
  let ρ : MatrixRepresentation H (Fin 7) := i ≫ quotRep k
  obtain ⟨v, hv0, hv⟩ := hU (Fin 7) ρ
  let W : Submodule k (Fin 8 → k) :=
    (MatrixRepresentation.fixedSubmodule ρ).comap (projLin k)
  have hWg : ∀ g : (CayleyDatum.split k).automorphismSubgroup (RingHom.id k), ∀ w ∈ W,
      ((g : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *ᵥ w ∈ W := by
    intro g w hw
    change projLin k (((g : GL (Fin 8) k) : Matrix (Fin 8) (Fin 8) k) *ᵥ w) ∈
      MatrixRepresentation.fixedSubmodule ρ
    rw [← quotMatrix_mulVec_projLin (mulVec_unit_of_mem g.2)]
    exact quotMatrix_mulVec_mem_fixedSubmodule i hN g hw
  have hsingle := stableSubspace k W
    (fun α r w hw => hWg ⟨rootGL α r, mem_automorphismSubgroup_id_iff.2
      (isAutomorphism_rootGL α r)⟩ w hw)
    (fun s t w hw => hWg ⟨torusGL s t, mem_automorphismSubgroup_id_iff.2
      (isAutomorphism_torusGL s t)⟩ w hw)
    ⟨sectLin k v, by
      change projLin k (sectLin k v) ∈ MatrixRepresentation.fixedSubmodule ρ
      rw [projLin_sectLin]
      exact hv, fun hmem => hv0 (by
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
        rw [← projLin_sectLin v, ← ha, map_smul, projLin_unit, smul_zero])⟩
  have hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
      pointsEquiv k T (h ≫ i.hom.hom) = 1 := by
    intro T h
    set g := pointsEquiv k T (h ≫ i.hom.hom)
    have hg := (mem_automorphismSubgroup_split_iff _ _).1 g.2
    have hcol : ∀ j : Fin 8, j ≠ 0 → j ≠ 7 → ∃ c : Γ(T.left, ⊤),
        ((g : GL (Fin 8) Γ(T.left, ⊤)) : Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤)) *ᵥ
          Pi.single j 1 = Pi.single j 1 + c • unit Γ(T.left, ⊤) := by
      intro j hj0 hj7
      have hj' : ρ.IsFixedVector (projLin k (Pi.single j 1)) := hsingle j hj0 hj7
      have hj := hj' T h
      rw [MatrixRepresentation.pointMatrix_apply] at hj
      dsimp only [ρ] at hj
      rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_quotRep, quotHom_val,
        projLin_map] at hj
      have hs : (fun l => scalarMap T ((Pi.single j (1 : k) : Fin 8 → k) l)) =
          (Pi.single j 1 : Fin 8 → Γ(T.left, ⊤)) := by
        funext l
        by_cases hl : l = j
        · subst hl
          simp
        · simp [hl]
      rw [hs, quotMatrix_mulVec_projLin hg.1, ← sub_eq_zero, ← map_sub] at hj
      refine ⟨((((g : GL (Fin 8) Γ(T.left, ⊤)) : Matrix (Fin 8) (Fin 8) Γ(T.left, ⊤)) *ᵥ
        Pi.single j 1 - Pi.single j 1 : Fin 8 → Γ(T.left, ⊤)) 0), ?_⟩
      rw [← eq_smul_unit_of_projLin_eq_zero hj, add_sub_cancel]
    have h1 := unitRigidity Γ(T.left, ⊤) _ hg hcol
    exact Subtype.ext (Units.ext h1)
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    apply (pointsEquiv k T).injective
    rw [hfix, map_one]
  · rintro rfl
    exact Subgroup.one_mem _

end Radical

/-! ### Connected reductive -/

section Reductive

variable (K)

/-- The automorphism group scheme of Zorn's split Cayley algebra over a field is connected
reductive. -/
theorem isConnectedReductive :
    IsConnectedReductive (CayleyDatum.split K).automorphismGroup where
  smooth := smooth_automorphismGroup
  isAffineHom := inferInstance
  connectedSpace := connectedSpace_automorphismGroup K
  hasTrivialGeometricUnipotentRadical :=
    HasTrivialUnipotentRadical.of_iso (baseChangeModelIso (toAlgebraicClosure K))
      (hasTrivialUnipotentRadical_of_isAlgClosed (AlgebraicClosure K))

end Reductive

end SplitCayley

end Langlands.GroupScheme
