import Langlands.GroupScheme.CentralIsogeny.CorootCompatibility
import Langlands.GroupScheme.CentralSurjection.TorusImage
import Langlands.GroupScheme.Rational.SplitTorusSurjection
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.CentralIsogeny.TorusRestriction
import Langlands.LinearAlgebra.RootDatumIsogeny

/-! # Scaled coroot compatibility in an fppf torus square -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.LinearAlgebra

/-- A reflection specified after multiplication by a nonzero integer has the expected
functional if its product with the comparison reflection has finite order. -/
theorem eq_functional_of_finiteOrder_scaled_reflections
    {M : Type*} [AddCommGroup M] (x : M) (q : ℤ) (hq : q ≠ 0)
    (f g : M →ₗ[ℤ] ℤ) (s t : M ≃ₗ[ℤ] M)
    (hf : f x = q * 2) (hg : g x = 2)
    (hs : ∀ y, q • s y = q • y - f y • x)
    (ht : ∀ y, t y = y - g y • x)
    (hst : IsOfFinOrder (s * t)) : f = q • g := by
  let p := s * t
  let d : M →ₗ[ℤ] ℤ := q • g - f
  have hdx : d x = 0 := by simp [d, hf, hg]
  have hp (y : M) : q • p y = q • y + d y • x := by
    change q • s (t y) = _
    rw [hs, ht, map_sub, map_smul, hf]
    simp only [d, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  have hdp (y : M) : d (p y) = d y := by
    have h := congrArg d (hp y)
    simp only [map_smul, map_add, hdx, smul_eq_mul, mul_zero, add_zero] at h
    exact mul_left_cancel₀ hq h
  have hdpow (n : ℕ) (y : M) : d ((p ^ n) y) = d y := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, hdp, ih]
  have hpow (n : ℕ) (y : M) :
      q • (p ^ n) y = q • y + (n : ℤ) • (d y • x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, hp, ih, hdpow]
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
  obtain ⟨n, hn, hnp⟩ := hst.exists_pow_eq_one
  have hn0 : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn.ne'
  ext y
  have he := hpow n y
  change q • ((s * t) ^ n) y = _ at he
  rw [hnp] at he
  have hz : (n : ℤ) • (d y • x) = 0 := by
    have := congrArg (fun z : M => z - q • y) he
    simpa using this.symm
  have hscalar := congrArg g hz
  simp only [map_smul, hg, map_zero, smul_eq_mul] at hscalar
  have hdy : d y = 0 := by
    have := (mul_eq_zero.mp hscalar).resolve_left hn0
    exact (mul_eq_zero.mp this).resolve_right (by norm_num)
  exact (sub_eq_zero.mp hdy).symm

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ H}
  {φ : G ⟶ H} {t : T ⟶ T'}

/-- The automorphism descended through an fppf torus image commutes with the actual
torus homomorphism, for any supplied source normalizer automorphism. -/
theorem IsFppfTorusImage.normalizerAut_comp
    (h : IsFppfTorusImage φ i i' t)
    (n : normalizerPoints i) {σ : T ≅ T} (hn : IsNormalizingPoint i n.val σ) :
    σ.hom ≫ t = t ≫ (h.normalizerAut n).hom := by
  let : IsClosedImmersion i'.hom.hom.left := h.isClosedSubgroup
  let : Mono i'.hom.hom := Over.mono_of_mono_left _
  have ht := h.isNormalizingPoint_normalizerAut n
  have he :
      CommGroupScheme.groupHom (σ.hom ≫ t) ≫ i' =
        CommGroupScheme.groupHom (t ≫ (h.normalizerAut n).hom) ≫ i' := by
    calc
      _ = (CommGroupScheme.groupHom σ.hom ≫ i) ≫ φ := by
        change (CommGroupScheme.groupHom σ.hom ≫ CommGroupScheme.groupHom t) ≫ i' = _
        rw [Category.assoc, h.comp_eq, Category.assoc]
      _ = (i ≫ (G.innerIso n.val).hom) ≫ φ := by rw [hn]
      _ = (CommGroupScheme.groupHom t ≫ i') ≫
          (H.innerIso (n.val ≫ φ.hom.hom)).hom := by
        rw [Category.assoc, innerIso_hom_comp, ← Category.assoc, ← h.comp_eq]
      _ = _ := by
        rw [Category.assoc, ht]
        rfl
  have hf := (show (SubgroupFunctor.range i').IsRepresentedBy i' from
    ⟨inferInstance, rfl⟩).hom_ext he
  exact congrArg Additive.ofMul hf

section Coroot

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {J : Type v} {J' : Type w}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}

/-- A positive scaled root equation forces the corresponding scaled coroot equation
in an fppf torus square whose target normalizer image is finite. -/
theorem IsRootDatumOf.coroot_comp_of_finite_weylImage_scaled
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) (hF : IsFppfTorusImage φ i i' t)
    [Mono i'.hom.hom.left] [Finite (weylImage i')]
    {j : J} {j' : J'} {q : ℕ} (hq : 0 < q)
    (hroot : t ≫ Q.root j' = (q : ℤ) • P.root j) :
    P.coroot j ≫ t = (q : ℤ) • Q.coroot j' := by
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := hF.flat
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := hF.surjective
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hinj : Function.Injective (fun χ : characterLattice T' => t ≫ χ) :=
    RealTorusSpace.characterRestrict_injective_of_epi t
  have hpair : latticePairing T (P.root j) (P.coroot j) = 2 := by
    rw [← hP.1]
    exact P.root_coroot_two j
  let e := latticeReflectionIso (P.root j) (P.coroot j) hpair
  obtain ⟨n, hn⟩ := hP.exists_normalizing_latticeReflectionIso i hT j
  let n₀ : normalizerPoints i := ⟨n, ⟨e, hn⟩⟩
  let τ := hF.normalizerAut n₀
  have hn' : IsNormalizingPoint i' (n ≫ φ.hom.hom) τ :=
    hF.isNormalizingPoint_normalizerAut n₀
  have hcomp : e.hom ≫ t = t ≫ τ.hom := hF.normalizerAut_comp n₀ hn
  have hinv : e.inv ≫ t = t ≫ τ.inv := by
    calc
      e.inv ≫ t = (e.inv ≫ (t ≫ τ.hom)) ≫ τ.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = (e.inv ≫ (e.hom ≫ t)) ≫ τ.inv := by rw [← hcomp]
      _ = t ≫ τ.inv := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hact (χ : characterLattice T') :
      t ≫ characterAut τ χ = characterAut e (t ≫ χ) := by
    change t ≫ (τ.inv ≫ χ) = e.inv ≫ (t ≫ χ)
    rw [← Category.assoc, ← hinv, Category.assoc]
  let f := (latticePairing T').flip (P.coroot j ≫ t)
  let g := (latticePairing T').flip (Q.coroot j')
  have htrans (χ : characterLattice T') :
      latticePairing T (t ≫ χ) (P.coroot j) = f χ := by
    change gmEndEquiv k (P.coroot j ≫ (t ≫ χ)) =
      gmEndEquiv k ((P.coroot j ≫ t) ≫ χ)
    rw [Category.assoc]
  have hf : f (Q.root j') = (q : ℤ) * 2 := by
    rw [← htrans, hroot]
    rw [map_smul, LinearMap.smul_apply, hpair]
    rfl
  have hg : g (Q.root j') = 2 := by
    change latticePairing T' (Q.root j') (Q.coroot j') = 2
    rw [← hQ.1]
    exact Q.root_coroot_two j'
  have hs (χ : characterLattice T') :
      (q : ℤ) • characterAut τ χ = (q : ℤ) • χ - f χ • Q.root j' := by
    apply hinj
    change t ≫ ((q : ℤ) • characterAut τ χ) =
      t ≫ ((q : ℤ) • χ - f χ • Q.root j')
    rw [Preadditive.comp_sub, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
      Preadditive.comp_zsmul, hact, hroot]
    rw [characterAut_latticeReflectionIso, htrans]
    module
  obtain ⟨m, υ, hm, hυ⟩ := hQ.2.2 j'
  let n' : normalizerPoints i' := ⟨n ≫ φ.hom.hom, ⟨τ, hn'⟩⟩
  let m' : normalizerPoints i' := ⟨m, ⟨υ, hm⟩⟩
  have hsn : weylAction i' n' = characterAut τ := by
    ext χ
    exact weylAction_eq i' (n := n') (σ := τ) hn' χ
  have htm : weylAction i' m' = Q.reflection j' := by
    ext χ
    rw [weylAction_eq i' (n := m') (σ := υ) hm χ]
    change characterAut υ χ = _
    rw [hυ]
  let a : weylImage i' := ⟨weylAction i' n', n', rfl⟩
  let b : weylImage i' := ⟨weylAction i' m', m', rfl⟩
  have horder : IsOfFinOrder (characterAut τ * Q.reflection j') := by
    have hfin := (weylImage i').subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))
    change IsOfFinOrder (weylAction i' n' * weylAction i' m') at hfin
    rwa [hsn, htm] at hfin
  have heq := Langlands.LinearAlgebra.eq_functional_of_finiteOrder_scaled_reflections
    (Q.root j') (q : ℤ) (by exact_mod_cast hq.ne') f g
    (characterAut τ) (Q.reflection j') hf hg hs
    (fun χ => by
      rw [RootPairing.reflection_apply]
      change χ - Q.toLinearMap χ (Q.coroot j') • Q.root j' = _
      rw [hQ.1]
      rfl) horder
  apply Q.flip.toPerfPair.injective
  ext χ
  change Q.toLinearMap χ (P.coroot j ≫ t) =
    Q.toLinearMap χ ((q : ℤ) • Q.coroot j')
  rw [hQ.1, map_smul]
  exact LinearMap.congr_fun heq χ

/-- The scaled coroot comparison for an actual isogeny of specified split tori.
No centrality or reductivity hypothesis on the ambient groups is required. -/
theorem IsRootDatumOf.coroot_comp_of_torusIsogeny_scaled
    [LocallyOfFiniteType H.X.hom]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi' : IsClosedSubgroup i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    {j : J} {j' : J'} {q : ℕ} (hq : 0 < q)
    (hroot : t ≫ Q.root j' = (q : ℤ) • P.root j) :
    P.coroot j ≫ t = (q : ℤ) • Q.coroot j' := by
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Finite (weylImage i') := splitTorusWeylImageFinite k H T' hT' i' hi'
  have hF : IsFppfTorusImage φ i i' t :=
    ⟨hi', hsquare.symm, ht.2.1, ht.2.2,
      locallyOfFinitePresentation_of_splitTori hT hT' t⟩
  exact hP.coroot_comp_of_finite_weylImage_scaled hQ hT hF hq hroot

/-- Actual character and cocharacter maps define a root-datum isogeny as soon as
the positive characteristic-power root comparison has been established. The coroot
comparison is deduced from the actual normalizers rather than supplied separately. -/
def IsRootDatumOf.rootDatumIsogenyOfRootFactors
    [LocallyOfFiniteType H.X.hom]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi' : IsClosedSubgroup i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    [Finite J] [Finite J'] [P.IsReduced] [Q.IsReduced]
    (p : ℕ) (hp : p = 1 ∨ Nat.Prime p)
    (e : J' ≃ J) (q : J' → ℕ)
    (hq : ∀ j', ∃ n : ℕ, q j' = p ^ n)
    (hroot : ∀ j', t ≫ Q.root j' = (q j' : ℤ) • P.root (e j')) :
    haveI := hT.finite_characterLattice
    haveI := hT.finite_cocharacterLattice
    haveI := hT'.finite_characterLattice
    haveI := hT'.finite_cocharacterLattice
    Langlands.LinearAlgebra.RootDatumIsogeny p Q P := by
  haveI := hT.finite_characterLattice
  haveI := hT.finite_cocharacterLattice
  haveI := hT'.finite_characterLattice
  haveI := hT'.finite_cocharacterLattice
  have : IsFinite (CommGroupScheme.groupHom t).hom.hom.left := ht.1
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hp_pos : 0 < p := hp.elim (fun h => by simp [h]) Nat.Prime.pos
  exact
    { characteristicExponent := hp
      weightMap := (characterRestrict (CommGroupScheme.groupHom t)).toIntLinearMap
      coweightMap := RealTorusSpace.cocharacterMapInt t
      indexEquiv := e
      weightMap_injective := RealTorusSpace.characterRestrict_injective_of_epi t
      coweightMap_injective := cocharacterMapInt_injective_of_isFinite t
      weight_coweight_transpose := by
        ext ν χ
        change P.toLinearMap (t ≫ χ) ν = Q.toLinearMap χ (ν ≫ t)
        rw [hP.1, hQ.1]
        exact congrArg (gmEndEquiv k) (Category.assoc ν t χ)
      rootFactor := q
      rootFactor_pow := hq
      root_weightMap := hroot
      coroot_coweightMap := fun j' =>
        hP.coroot_comp_of_torusIsogeny_scaled hQ hT hT' hi' ht hsquare
          (by obtain ⟨n, hn⟩ := hq j'; rw [hn]; exact pow_pos hp_pos n) (hroot j') }

/-- Both maps of the constructed root-datum isogeny are the actual lattice maps. -/
theorem IsRootDatumOf.rootDatumIsogenyOfRootFactors_spec
    [LocallyOfFiniteType H.X.hom]
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi' : IsClosedSubgroup i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    [Finite J] [Finite J'] [P.IsReduced] [Q.IsReduced]
    (p : ℕ) (hp : p = 1 ∨ Nat.Prime p)
    (e : J' ≃ J) (q : J' → ℕ)
    (hq : ∀ j', ∃ n : ℕ, q j' = p ^ n)
    (hroot : ∀ j', t ≫ Q.root j' = (q j' : ℤ) • P.root (e j')) :
    haveI := hT.finite_characterLattice
    haveI := hT.finite_cocharacterLattice
    haveI := hT'.finite_characterLattice
    haveI := hT'.finite_cocharacterLattice
    let f := hP.rootDatumIsogenyOfRootFactors hQ hT hT' hi' ht hsquare p hp e q hq hroot
    (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧
      (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end Coroot

end Langlands.GroupScheme
