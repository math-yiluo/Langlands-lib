import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.MultiplicativeLaurent
import Langlands.GroupScheme.HomConjugacy

/-! # Normalizing points in dynamic and standard parabolics

A rational point normalizing a split subtorus `i : T ⟶ G` that lies in the dynamic parabolic
`P_G(ζ)` of a cocharacter `ζ` of `T` centralizes `ζ`. Consequently, the normalizing points in the
standard parabolic `P_J(k)` all lie in the standard Levi `L_J(k)`, and their classes lie in
`W_J`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Power maps of `𝔾_m` do not extend to the affine line -/

section GmExtension

variable (k : Type u) [CommRing k] [IsDomain k]

/-- Over a domain `k`, the power map `t ↦ t ^ m` of `𝔾_{m,k}` extends along
`𝔾_{m,k} ⊆ 𝔸¹_k` to a morphism `𝔸¹_k ⟶ 𝔾_{m,k}` only when `m = 0`. -/
theorem Gm.eq_zero_of_zpow_extension (m : ℤ)
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶
      (Gm (Spec (CommRingCat.of k))).X)
    (he : Over.mk (𝟙 (Spec (CommRingCat.of k))) ◁ AffineLine.unitInclusion _ ≫ e =
      snd (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (Gm (Spec (CommRingCat.of k))).X ^ m) :
    m = 0 := by
  let A := CommRingCat.of k
  let f : Spec A ⟶ Spec A := 𝟙 _
  let p : AffineLine.laurentScheme f ⟶ (Gm (Spec A)).X :=
    (Gm.pointsEquiv _ _).symm (AffineLine.laurentUnit f)
  have h1 : AffineLine.laurentInclusion f ≫ AffineLine.polynomialPoint f ≫ e = p ^ m := by
    rw [← Category.assoc, AffineLine.laurentInclusion_polynomialPoint, Category.assoc, he,
      GrpObj.comp_zpow, lift_snd]
  have h2 := Gm.affinePointsEquiv_naturality (AffineLine.polynomialToLaurent A)
    (Spec.map (AffineLine.polynomialC A) ≫ f) (AffineLine.polynomialPoint f ≫ e)
  change Gm.affinePointsEquiv _ (AffineLine.laurentInclusion f ≫ _) = _ at h2
  have h3 : Gm.affinePointsEquiv
      (Spec.map (AffineLine.polynomialToLaurent A) ≫ (AffineLine.polynomialScheme f).hom) p =
        Gm.relativeCoordUnit k := by
    apply Units.ext
    rw [Gm.affinePointsEquiv_val]
    change (Scheme.ΓSpecIso _).hom ((Gm.pointsEquiv _ (AffineLine.laurentScheme f))
      ((Gm.pointsEquiv _ (AffineLine.laurentScheme f)).symm (AffineLine.laurentUnit f))).val = _
    rw [MulEquiv.apply_symm_apply, AffineLine.laurentUnit, Units.coe_map]
    change (Scheme.ΓSpecIso _).hom ((Scheme.ΓSpecIso _).inv _) = _
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  rw [h1, map_zpow, h3] at h2
  have h4 := congrArg Units.val h2
  simp only [Units.coe_map, Gm.relativeCoordUnit_zpow_val] at h4
  set u := Gm.affinePointsEquiv (Spec.map (AffineLine.polynomialC A) ≫ f)
    (AffineLine.polynomialPoint f ≫ e)
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.1 (u.isUnit : IsUnit (u : Polynomial k))
  change _ = (Polynomial.toLaurent (u : Polynomial k) : LaurentPolynomial k) at h4
  rw [← hcu, Polynomial.toLaurent_C] at h4
  have hdeg := congrArg LaurentPolynomial.degree h4
  rw [LaurentPolynomial.degree_C hc.ne_zero, LaurentPolynomial.degree_T] at hdeg
  exact_mod_cast hdeg

end GmExtension

/-! ### Cocharacters of split tori are detected by the pairing -/

section SplitPairing

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A cocharacter of a split torus pairing trivially with every character is zero. -/
theorem IsSplitTorus.cocharacter_eq_zero (hT : IsSplitTorus T.toGrp) {δ : cocharacterLattice T}
    (h : ∀ α : characterLattice T, latticePairing T α δ = 0) : δ = 0 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have := hI
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  apply (cocharacterLattice.congr eC).injective
  rw [map_zero]
  apply (LinearMap.IsPerfPair.bijective_right
    (latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))).injective
  rw [map_zero]
  ext α
  rw [LinearMap.flip_apply, LinearMap.zero_apply,
    ← (characterLattice.congr eC).apply_symm_apply α, latticePairing_congr]
  exact h _

end SplitPairing

/-! ### Normalizing points in dynamic parabolics -/

section Normalizer

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- On points, a difference of homomorphisms acts by the quotient of the values. -/
private theorem comp_groupHom_sub {H K : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : Over (Spec (CommRingCat.of k))} (x : U ⟶ H.X) (f g : H ⟶ K) :
    x ≫ (CommGroupScheme.groupHom (f - g)).hom.hom =
      (x ≫ (CommGroupScheme.groupHom f).hom.hom) * (x ≫ (CommGroupScheme.groupHom g).hom.hom)⁻¹ :=
  (congrArg Additive.toMul ((evalPoint x).map_sub f g)).trans (div_eq_mul_inv _ _)

/-- A rational point normalizing a split subtorus `i : T ⟶ G` and lying in the dynamic
parabolic of a cocharacter `ζ` of `T` lies in the dynamic centralizer of `ζ`. -/
theorem IsSplitSubtorus.mem_centralizer_of_mem_parabolic (hi : IsSplitSubtorus i)
    (ζ : cocharacterLattice T) {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : n ∈ normalizerPoints i)
    (hp : n ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    n ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  obtain ⟨σ, hσ⟩ := hn
  obtain ⟨e, he⟩ := hp
  have : IsClosedImmersion i.hom.hom.left := hi.2
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let U₀ := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let δ : cocharacterLattice T := ζ ≫ σ.inv - ζ
  let t := snd U₀ (Gm (Spec (CommRingCat.of k))).X
  let c := fst U₀ (Gm (Spec (CommRingCat.of k))).X ≫ n
  -- Conjugation by `n` restricts to `σ` on `T`.
  have hc : c = G.constantPoint n (U₀ ⊗ (Gm (Spec (CommRingCat.of k))).X) := by
    rw [← G.constantPoint_naturality n (fst U₀ (Gm (Spec (CommRingCat.of k))).X)]
    exact congrArg (fst U₀ (Gm (Spec (CommRingCat.of k))).X ≫ ·) (G.constantPoint_self n).symm
  have hconj : ∀ y : U₀ ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ T.X,
      c * (y ≫ i.hom.hom) * c⁻¹ =
        y ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫ i.hom.hom := by
    intro y
    have h := congrArg (fun φ : T.toGrp ⟶ G => y ≫ φ.hom.hom) hσ
    simp only [Grp.comp_hom_hom] at h
    rw [← Category.assoc, comp_innerIso_hom, ← hc] at h
    exact h
  -- The orbit of `n`, translated by `n⁻¹`, is the image of the cocharacter `δ`.
  have hkey : c⁻¹ * Dynamic.orbit (CommGroupScheme.groupHom ζ ≫ i) n =
      t ≫ (CommGroupScheme.groupHom δ).hom.hom ≫ i.hom.hom := by
    have hy := hconj (t ≫ (CommGroupScheme.groupHom (ζ ≫ σ.inv)).hom.hom)
    rw [← Category.assoc (t ≫ _), ← comp_groupHom_comp, Category.assoc ζ, Iso.inv_hom_id,
      Category.comp_id] at hy
    rw [← Category.assoc, comp_groupHom_sub, MonObj.mul_comp, GrpObj.inv_comp]
    simp only [Dynamic.orbit, Grp.comp_hom_hom]
    change c⁻¹ * ((t ≫ (CommGroupScheme.groupHom ζ).hom.hom ≫ i.hom.hom) * c *
      (t ≫ (CommGroupScheme.groupHom ζ).hom.hom ≫ i.hom.hom)⁻¹) = _
    rw [← Category.assoc t, ← hy]
    group
  -- The translated extension lands in the closed subgroup `T`.
  let e₁ := (fst U₀ (AffineLine.scheme (Spec (CommRingCat.of k))) ≫ n)⁻¹ * e
  have he₁ : U₀ ◁ AffineLine.unitInclusion _ ≫ e₁ =
      (t ≫ (CommGroupScheme.groupHom δ).hom.hom) ≫ i.hom.hom := by
    rw [Category.assoc, ← hkey, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst_assoc]
    rw [Dynamic.IsOrbitExtension] at he
    rw [he]
  obtain ⟨e', he'⟩ := AffineLine.exists_lift_of_unitInclusion i.hom.hom e₁ _ he₁.symm
  have hlift : U₀ ◁ AffineLine.unitInclusion _ ≫ e' = t ≫ (CommGroupScheme.groupHom δ).hom.hom := by
    rw [← cancel_mono i.hom.hom, Category.assoc, he', he₁]
  -- Every character pairs trivially with `δ`.
  have hpair : ∀ α : characterLattice T, latticePairing T α δ = 0 := by
    intro α
    apply Gm.eq_zero_of_zpow_extension k _ (e' ≫ (CommGroupScheme.groupHom α).hom.hom)
    rw [← Category.assoc, hlift, ← comp_groupHom_comp, latticePairing_apply,
      ← gmEndEquiv_symm_comp, AddEquiv.symm_apply_apply]
  have hδ : δ = 0 := hi.1.cocharacter_eq_zero hpair
  rw [hδ, ← Category.assoc, comp_groupHom_zero, MonObj.one_comp] at hkey
  rw [Dynamic.mem_centralizer]
  exact (inv_mul_eq_one.mp hkey).symm

variable [IsAffineHom G.X.hom]

/-- The rational points of the standard parabolic `P_J(k)` that normalize a split subtorus lie
in the standard Levi `L_J(k)`. -/
theorem IsSplitSubtorus.normalizerPoints_inf_standardParabolicPoints_le (hi : IsSplitSubtorus i)
    (ν : cocharacterLattice T) (J : Set (characterLattice T)) :
    normalizerPoints i ⊓ standardParabolicPoints i ν J ≤ standardLeviPoints i ν J := by
  rintro n ⟨hn, hp⟩
  rw [mem_standardLevi]
  intro ζ hζ
  exact hi.mem_centralizer_of_mem_parabolic ζ hn ((mem_standardParabolic i ν).1 hp ζ hζ)

/-- For a normalizing point `n` of a split subtorus, membership in `P_J(k)`, membership in
`L_J(k)` and membership of its class in `W_J` are equivalent. -/
theorem IsSplitSubtorus.mem_standardParabolicPoints_iff (hi : IsSplitSubtorus i)
    (ν : cocharacterLattice T) (J : Set (characterLattice T)) (n : normalizerPoints i) :
    ((n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ standardParabolicPoints i ν J ↔
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ standardLeviPoints i ν J) ∧
    ((n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ standardLeviPoints i ν J ↔
      (QuotientGroup.mk n : relativeWeylGroup i) ∈ standardRelativeWeylGroup i ν J) := by
  refine ⟨⟨fun h => hi.normalizerPoints_inf_standardParabolicPoints_le ν J ⟨n.2, h⟩,
    fun h => standardLevi_le_standardParabolic i ν J _ h⟩,
    ⟨fun h => (mem_standardRelativeWeylGroup_iff i ν).2 ⟨n, h, rfl⟩, fun h => ?_⟩⟩
  obtain ⟨m, hm, hmn⟩ := (mem_standardRelativeWeylGroup_iff i ν).1 h
  have hz : ((m⁻¹ * n : normalizerPoints i) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      centralizerPoints i :=
    Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hmn)
  have hzL : ((m⁻¹ * n : normalizerPoints i) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      standardLeviPoints i ν J := by
    apply torusCentralizer_le_standardLevi i ν J
    rw [mem_torusCentralizer_base_iff]
    exact (mem_centralizerPoints i).1 hz
  have hmem := (standardLeviPoints i ν J).mul_mem hm hzL
  rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at hmem

/-- The class of a normalizing point in `P_J(k)` lies in `W_J`. -/
theorem IsSplitSubtorus.mk_mem_standardRelativeWeylGroup (hi : IsSplitSubtorus i)
    (ν : cocharacterLattice T) (J : Set (characterLattice T)) {n : normalizerPoints i}
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ standardParabolicPoints i ν J) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈ standardRelativeWeylGroup i ν J :=
  ((hi.mem_standardParabolicPoints_iff ν J n).2.1) ((hi.mem_standardParabolicPoints_iff ν J n).1.1 hn)

end Normalizer

end Langlands.GroupScheme
