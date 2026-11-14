import Langlands.Geometry.Building.Kottwitz.CocenterCocharacterKernel
import Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionStatement
import Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof

/-! # Torsion kernel of the cocenter inertia map, from the fundamental-group statements -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section Coinvariants

variable {Γ V W : Type*} [Monoid Γ] [AddCommGroup V] [Module ℤ V]
  [AddCommGroup W] [Module ℤ W]
  {ρ : Representation ℤ Γ V} {τ : Representation ℤ Γ W}

/-- A surjective equivariant map carries the coinvariant kernel onto the coinvariant kernel. -/
theorem coinvariantsKer_le_map (ψ : V →ₗ[ℤ] W) (hsurj : Function.Surjective ψ)
    (heq : ∀ g v, ψ (ρ g v) = τ g (ψ v)) :
    Representation.Coinvariants.ker τ ≤ (Representation.Coinvariants.ker ρ).map ψ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, w⟩, rfl⟩
  obtain ⟨v, rfl⟩ := hsurj w
  exact ⟨ρ g v - v, Representation.Coinvariants.sub_mem_ker g v, by
    change ψ (ρ g v - v) = τ g (ψ v) - ψ v
    rw [map_sub, heq]⟩

/-- If a surjective equivariant map has torsion kernel, then so does every map on
coinvariants that it induces. -/
theorem coinvariants_exists_nsmul_eq_zero (ψ : V →ₗ[ℤ] W) (hsurj : Function.Surjective ψ)
    (heq : ∀ g v, ψ (ρ g v) = τ g (ψ v))
    (htor : ∀ v, ψ v = 0 → ∃ n : ℕ, 0 < n ∧ n • v = 0)
    (φ : Representation.Coinvariants ρ →ₗ[ℤ] Representation.Coinvariants τ)
    (hφ : ∀ v, φ (Representation.Coinvariants.mk ρ v) =
      Representation.Coinvariants.mk τ (ψ v))
    (y : Representation.Coinvariants ρ) (hy : φ y = 0) :
    ∃ n : ℕ, 0 < n ∧ n • y = 0 := by
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective ρ y
  rw [hφ, Representation.Coinvariants.mk_eq_zero] at hy
  obtain ⟨w, hw, hψw⟩ := coinvariantsKer_le_map ψ hsurj heq hy
  obtain ⟨n, hn, hnx⟩ := htor (x - w) (by rw [map_sub, hψw, sub_self])
  refine ⟨n, hn, ?_⟩
  have hxw : n • x = n • w := by
    rw [smul_sub, sub_eq_zero] at hnx
    exact hnx
  rw [← map_nsmul, hxw, map_nsmul, (Representation.Coinvariants.mk_eq_zero ρ).2 hw,
    smul_zero]

end Coinvariants

section SelectedMaps

variable (k K E : Type u) [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
  [Normal k K] [IsSepClosure k E]

/-- The selection law of the induced inertia map, from Galois equivariance of the
induced map on algebraic fundamental groups. -/
theorem fundamentalInertiaMap_spec_of_statement
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsConnectedReductive H) (f : H ⟶ G) :
    IsFundamentalInertiaMap k K E G hG H hH f (fundamentalInertiaMap k K E G hG H hH f) :=
  Classical.epsilon_spec ⟨Representation.Coinvariants.map _ _
    { toLinearMap := fundamentalGroupMap k E H G hH hG f
      isIntertwining' := fun σ => LinearMap.ext fun x =>
        (hfund k E H G hH hG (chosenChoice k H hH) (chosenChoice k G hG) f).2.2.1 σ.val x },
    fun _ => rfl⟩

/-- The selection law of the torus inertia comparison, from Galois equivariance of the
published torus fundamental comparison. -/
theorem torusInertiaComparison_spec
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp) :
    IsTorusInertiaComparison k K E T hT (torusInertiaComparison k K E T hT) :=
  Classical.epsilon_spec ⟨Representation.Coinvariants.map _ _
    { toLinearMap := torusFundamentalComparison k E T hT
      isIntertwining' := fun σ => LinearMap.ext fun x =>
        (torusFundamentalComparison_proof k E T hT).2.2.2 σ.val x },
    fun _ => rfl⟩

end SelectedMaps

section CocenterFundamental

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (c : Cocenter k G) (E : Type u) [Field E] [Algebra k E]

/-- The map `π₁(G) → π₁(D) → X_*(D)` induced by the actual cocenter quotient,
followed by the selected torus comparison. -/
def Cocenter.fundamentalCocharacterMap :
    fundamentalGroup k G E hG →ₗ[ℤ] geometricCocharacters k E c.torus :=
  (torusFundamentalComparison k E c.torus c.isTorus).comp
    (fundamentalGroupMap k E G c.torus.toGrp hG
      c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient)

variable [IsSepClosure k E]

/-- On representatives, the fundamental cocharacter map is the cocharacter map of the
restriction `T → D` of the cocenter quotient to the chosen maximal torus. -/
theorem Cocenter.fundamentalCocharacterMap_projection
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (ν : (chosenChoice k G hG).lattice E) :
    c.fundamentalCocharacterMap hG E ((chosenChoice k G hG).projection E ν) =
      c.torusCocharacterMap (chosenChoice k G hG) E ν := by
  let a := chosenChoice k G hG
  let hD := c.isTorus.isConnectedReductive_of_fieldSplitting
  let b := chosenChoice k c.torus.toGrp hD
  let BC := CommGroupScheme.baseChange (algebraBaseMap k E)
  let : IsIso b.inclusion := b.isMaximal.isIso_of_torus c.isTorus
  let d : a.torus ⟶ b.torus := Additive.ofMul (a.inclusion ≫ c.quotient ≫ inv b.inclusion)
  have hd : d ≫ (Additive.ofMul b.inclusion : b.torus ⟶ c.torus) = c.torusMap a := by
    change Additive.ofMul ((a.inclusion ≫ c.quotient ≫ inv b.inclusion) ≫ b.inclusion) =
      Additive.ofMul (a.inclusion ≫ c.quotient)
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hf : a.IsTorusFactorization E b c.quotient (BC.map d) := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map c.quotient =
      (GroupScheme.baseChange (algebraBaseMap k E)).map
        (a.inclusion ≫ c.quotient ≫ inv b.inclusion) ≫
      (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hm := (hfund k E G c.torus.toGrp hG hD a b c.quotient).2.1.2 b _ hf ν
  rw [(hcmp k E c.torus.toGrp hD).2.1 b, LinearMap.id_apply] at hm
  change torusFundamentalComparison k E c.torus c.isTorus
    (a.mapTo E b c.quotient (a.projection E ν)) = _
  rw [hm, (torusFundamentalComparison_proof k E c.torus c.isTorus).2.1]
  change (ν ≫ BC.map d) ≫ BC.map (Additive.ofMul b.inclusion) = ν ≫ BC.map (c.torusMap a)
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hd]

/-- The fundamental cocharacter map is Galois equivariant. -/
theorem Cocenter.fundamentalCocharacterMap_galois
    (hfund : AlgebraicFundamentalGroupMapStatement.{u}) (σ : E ≃ₐ[k] E)
    (x : fundamentalGroup k G E hG) :
    c.fundamentalCocharacterMap hG E (fundamentalGroupGalois k G E hG σ x) =
      cocharacterLattice.galoisRepresentation k E c.torus σ
        (c.fundamentalCocharacterMap hG E x) := by
  change torusFundamentalComparison k E c.torus c.isTorus
      (fundamentalGroupMap k E G c.torus.toGrp hG
        c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient
        (fundamentalGroupGalois k G E hG σ x)) = _
  rw [show fundamentalGroupMap k E G c.torus.toGrp hG
        c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient
        (fundamentalGroupGalois k G E hG σ x) =
      fundamentalGroupGalois k c.torus.toGrp E
        c.isTorus.isConnectedReductive_of_fieldSplitting σ
        (fundamentalGroupMap k E G c.torus.toGrp hG
          c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient x) from
    (hfund k E G c.torus.toGrp hG c.isTorus.isConnectedReductive_of_fieldSplitting
      (chosenChoice k G hG) (chosenChoice k c.torus.toGrp
        c.isTorus.isConnectedReductive_of_fieldSplitting) c.quotient).2.2.1 σ x]
  exact (torusFundamentalComparison_proof k E c.torus c.isTorus).2.2.2 σ _

end CocenterFundamental

section SeparableClosure

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (c : Cocenter k G)

/-- Over the separable closure the fundamental cocharacter map is surjective. -/
theorem Cocenter.fundamentalCocharacterMap_surjective
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u}) :
    Function.Surjective (c.fundamentalCocharacterMap hG (SeparableClosure k)) := by
  intro w
  obtain ⟨ν, rfl⟩ := c.torusCocharacterMap_surjective (chosenChoice k G hG) w
  exact ⟨_, c.fundamentalCocharacterMap_projection hG (SeparableClosure k) hcmp hfund ν⟩

/-- Over the separable closure the fundamental cocharacter map has torsion kernel. -/
theorem Cocenter.fundamentalCocharacterMap_torsion
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (x : fundamentalGroup k G (SeparableClosure k) hG)
    (hx : c.fundamentalCocharacterMap hG (SeparableClosure k) x = 0) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  let a := chosenChoice k G hG
  obtain ⟨ν, rfl⟩ := (a.corootImage (SeparableClosure k)).mkQ_surjective x
  change c.fundamentalCocharacterMap hG (SeparableClosure k)
    (a.projection (SeparableClosure k) ν) = 0 at hx
  rw [c.fundamentalCocharacterMap_projection hG (SeparableClosure k) hcmp hfund] at hx
  obtain ⟨n, hn, hmem⟩ := c.exists_pos_smul_mem_corootImage a ν hx
  refine ⟨n.toNat, by omega, ?_⟩
  have hsmul : n.toNat • ν = n • ν := by
    rw [← natCast_zsmul, Int.toNat_of_nonneg hn.le]
  rw [← map_nsmul, hsmul]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

end SeparableClosure

/-- The torsion-kernel property of the cocenter inertia map follows from the canonical
comparison and induced-map statements for algebraic fundamental groups. -/
theorem cocenterTargetTorsion_of_statements
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u}) :
    CocenterTargetTorsionStatement.{u} := by
  intro F _ _ _ _ G hG c y hy
  let K := UnramifiedClosure F
  let E := SeparableClosure F
  let hD := c.isTorus.isConnectedReductive_of_fieldSplitting
  rw [MonoidHom.mem_ker] at hy
  have h0 : cocenterTargetMap F F G hG c (Multiplicative.toAdd y) = 0 :=
    congrArg Multiplicative.toAdd hy
  have hφ : ∀ x, cocenterTargetMap F F G hG c (fundamentalInertiaProjection F K E G hG x) =
      inertiaProjection F K E (cocharacterLattice.galoisRepresentation F E c.torus)
        (c.fundamentalCocharacterMap hG E x) := by
    intro x
    change torusInertiaComparison F K E c.torus c.isTorus
      (fundamentalInertiaMap F K E c.torus.toGrp hD G hG c.quotient
        (fundamentalInertiaProjection F K E G hG x)) = _
    rw [fundamentalInertiaMap_spec_of_statement F K E hfund c.torus.toGrp hD G hG c.quotient x,
      torusInertiaComparison_spec F K E c.torus c.isTorus]
    rfl
  obtain ⟨n, hn, hny⟩ := coinvariants_exists_nsmul_eq_zero
    (c.fundamentalCocharacterMap hG E)
    (c.fundamentalCocharacterMap_surjective hG hcmp hfund)
    (fun σ x => c.fundamentalCocharacterMap_galois hG E hfund σ.val x)
    (c.fundamentalCocharacterMap_torsion hG hcmp hfund)
    (cocenterTargetMap F F G hG c) hφ (Multiplicative.toAdd y) h0
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨n, hn, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact hny

end Langlands.Geometry.Building.Kottwitz
