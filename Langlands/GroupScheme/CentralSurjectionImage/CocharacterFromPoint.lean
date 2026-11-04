import Langlands.GroupScheme.CentralSurjectionImage.EigenDatum
import Langlands.GroupScheme.CentralSurjectionImage.InseparableRigidity
import Langlands.GroupScheme.Torus.CocharacterDetection
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Cocharacters over the base field from a point of infinite order

Let `Z` be an affine commutative group scheme locally of finite type over a field `k`, and `χ` a
rational character. If some point of `Z` with values in an algebraically closed field takes a
value of infinite order under `χ`, then `χ` restricts nontrivially to a cocharacter of `Z` defined
over `k`. The eigen datum over `K[Kˣ]` is restricted to a finitely generated exponent group,
mapped to `ℤ`, and descended to `k`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {Z : CommGroupScheme (Spec (CommRingCat.of k))}

section Transport

variable {S : Type u} [CommRing S] [Algebra k S] {Λ Λ' : Type u} [AddCommGroup Λ]
  [AddCommGroup Λ']

/-- Cocharacter data are transported along homomorphisms of exponent groups. -/
theorem IsDatum.expMap {χ : characterLattice Z} {m : Λ}
    {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)} (hp : IsDatum χ m p) (φ : Λ →+ Λ') :
    IsDatum χ (φ m) (expMapG (G := Z.toGrp) φ p) where
  mult := by
    have h := congrArg (expMapG (G := Z.toGrp) (φ.prodMap φ)) hp.mult
    change expMapG (G := Z.toGrp) (diagHom Λ') (expMapG φ p) =
      expMapG (AddMonoidHom.inl Λ' Λ') (expMapG φ p) *
        expMapG (AddMonoidHom.inr Λ' Λ') (expMapG φ p)
    change expMapG (G := Z.toGrp) _ (expMapG (diagHom Λ) p) =
      expMapG _ (expMapG (AddMonoidHom.inl Λ Λ) p * expMapG (AddMonoidHom.inr Λ Λ) p) at h
    rw [map_mul, expMapG_expMapG, expMapG_expMapG, expMapG_expMapG] at h
    have e1 : (diagHom Λ').comp φ = (φ.prodMap φ).comp (diagHom Λ) := by
      ext <;> simp
    have e2 : (AddMonoidHom.inl Λ' Λ').comp φ = (φ.prodMap φ).comp (AddMonoidHom.inl Λ Λ) := by
      ext <;> simp
    have e3 : (AddMonoidHom.inr Λ' Λ').comp φ = (φ.prodMap φ).comp (AddMonoidHom.inr Λ Λ) := by
      ext <;> simp
    rw [expMapG_expMapG, expMapG_expMapG, expMapG_expMapG, e1, e2, e3]
    exact h
  value := by
    rw [expMapG, characterValue_affineMap, hp.value]
    apply Units.ext
    simp [AddMonoidAlgebra.mapDomain_single]

/-- **Restriction of exponents.** A cocharacter datum for an affine group scheme with finitely
generated coordinate algebra comes from a datum over `S[Γ]` for a finitely generated subgroup
`Γ` of the exponent group containing its weight. -/
theorem IsDatum.exists_restrict [IsAffine Z.toGrp.X.left] [Nontrivial S]
    (hfin : Algebra.FiniteType (CommRingCat.of k) (coordAlgebra Z.toGrp))
    {χ : characterLattice Z} {m : Λ} {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)}
    (hp : IsDatum χ m p) :
    ∃ (Γ : AddSubgroup Λ) (hm : m ∈ Γ), Γ.FG ∧
      ∃ p' : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Γ), IsDatum χ ⟨m, hm⟩ p' := by
  classical
  obtain ⟨s, hs⟩ := hfin.out
  let c := (coord p).hom
  let T : Finset Λ := s.biUnion fun b => (c b).coeff.support
  let Γ : AddSubgroup Λ := AddSubgroup.closure (T : Set Λ)
  have hsupp : ∀ b, ((c b).coeff.support : Set Λ) ⊆ Γ := by
    intro b
    have hb : b ∈ Algebra.adjoin (CommRingCat.of k) (s : Set (coordAlgebra Z.toGrp)) := by
      rw [hs]
      trivial
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      intro γ hγ
      exact AddSubgroup.subset_closure (Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨b, hb, hγ⟩))
    | algebraMap r =>
      rw [AlgHom.commutes, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply]
      intro γ hγ
      rw [AddMonoidAlgebra.coeff_single] at hγ
      rw [Finset.mem_coe] at hγ
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hγ)]
      exact Γ.zero_mem
    | add a b _ _ ha hb =>
      intro γ hγ
      rw [map_add, AddMonoidAlgebra.coeff_add] at hγ
      rcases Finset.mem_union.mp (Finsupp.support_add hγ) with h | h
      · exact ha h
      · exact hb h
    | mul a b _ _ ha hb =>
      intro γ hγ
      rw [map_mul] at hγ
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hγ)
      exact Γ.add_mem (ha hx) (hb hy)
  have hsub : Function.Injective (Γ.subtype : Γ → Λ) := Subtype.val_injective
  let f : AddMonoidAlgebra S Γ →ₐ[k] AddMonoidAlgebra S Λ :=
    AddMonoidAlgebra.mapDomainAlgHom k S Γ.subtype
  have hf : Function.Injective f := AddMonoidAlgebra.mapDomain_injective hsub
  obtain ⟨p', hp'⟩ := exists_affineMap_eq f hf p (fun b => by
    refine ⟨AddMonoidAlgebra.comapDomain Γ.subtype hsub (c b), ?_⟩
    change AddMonoidAlgebra.mapDomain Γ.subtype _ = c b
    apply AddMonoidAlgebra.mapDomain_comapDomain
    intro γ hγ
    exact ⟨⟨γ, hsupp b hγ⟩, rfl⟩)
  have hcm : c (charCoord χ) = AddMonoidAlgebra.single m 1 := by
    rw [← characterValue_eq_coord, hp.value, monomial_val]
  have hm : m ∈ Γ := by
    apply hsupp (charCoord χ)
    rw [hcm, AddMonoidAlgebra.coeff_single, Finset.mem_coe, Finsupp.mem_support_iff,
      Finsupp.single_eq_same]
    exact one_ne_zero
  refine ⟨Γ, hm, ⟨T, rfl⟩, p', ?_, ?_⟩
  · have hinj : Function.Injective
        (expMapG (G := Z.toGrp) (S := S) (Γ.subtype.prodMap Γ.subtype)) :=
      affineMap_injective _ (AddMonoidAlgebra.mapDomain_injective
        (Prod.map_injective.mpr ⟨hsub, hsub⟩))
    apply hinj
    change expMapG (G := Z.toGrp) _ (expMapG (diagHom Γ) p') =
      expMapG _ (expMapG (AddMonoidHom.inl Γ Γ) p' * expMapG (AddMonoidHom.inr Γ Γ) p')
    have hp'' : expMapG (G := Z.toGrp) Γ.subtype p' = p := hp'
    have e1 : (Γ.subtype.prodMap Γ.subtype).comp (diagHom Γ) = (diagHom Λ).comp Γ.subtype := by
      ext <;> simp
    have e2 : (Γ.subtype.prodMap Γ.subtype).comp (AddMonoidHom.inl Γ Γ) =
        (AddMonoidHom.inl Λ Λ).comp Γ.subtype := by
      ext <;> simp
    have e3 : (Γ.subtype.prodMap Γ.subtype).comp (AddMonoidHom.inr Γ Γ) =
        (AddMonoidHom.inr Λ Λ).comp Γ.subtype := by
      ext <;> simp
    rw [map_mul, expMapG_expMapG, expMapG_expMapG, expMapG_expMapG, e1, e2, e3,
      ← expMapG_expMapG, ← expMapG_expMapG, ← expMapG_expMapG, hp'']
    exact hp.mult
  · apply Units.map_injective (f := f.toMonoidHom) hf
    have h1 := characterValue_affineMap χ f p'
    rw [show Lie.affineMap Z.toGrp f p' = p from hp', hp.value] at h1
    rw [← h1]
    apply Units.ext
    simp [f, AddMonoidAlgebra.mapDomain_single]

end Transport

/-- A nontorsion element of a finitely generated abelian group is detected by a homomorphism to
`ℤ`. -/
theorem exists_addMonoidHom_int_ne_zero {A : Type u} [AddCommGroup A] (hA : AddGroup.FG A)
    {a : A} (ha : ∀ n : ℕ, n ≠ 0 → n • a ≠ 0) : ∃ φ : A →+ ℤ, φ a ≠ 0 := by
  have : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr hA
  let Q := A ⧸ Submodule.torsion ℤ A
  have hq : (Submodule.torsion ℤ A).mkQ a ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion_iff]
    rintro ⟨⟨n, hn⟩, hna⟩
    have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
    apply ha n.natAbs (Int.natAbs_ne_zero.mpr hn0)
    rcases Int.natAbs_eq n with h | h
    · rw [← natCast_zsmul, ← h]
      exact hna
    · rw [← natCast_zsmul, show ((n.natAbs : ℤ)) = -n by omega, neg_smul]
      change -(n • a) = 0 at *
      rw [show n • a = 0 from hna, neg_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℤ hq
  exact ⟨(φ ∘ₗ (Submodule.torsion ℤ A).mkQ).toAddMonoidHom, hφ⟩

/-- **Cocharacters from a point of infinite order.** Let `Z` be an affine commutative group scheme
locally of finite type over `k`, `χ` a rational character, and `x` a point of `Z` with values in
an algebraically closed field such that no positive power of `χ(x)` is `1`. Then some cocharacter
`𝔾_m ⟶ Z` over `k` restricts `χ` nontrivially. -/
theorem exists_gm_characterRestrict_ne_zero_of_point [IsAffineHom Z.toGrp.X.hom]
    [LocallyOfFiniteType Z.toGrp.X.hom] {χ : rationalCharacters Z.toGrp} {K : Type u} [Field K]
    [IsAlgClosed K] [Algebra k K] (x : Lie.AffinePoints Z.toGrp K)
    (hx : ∀ n : ℕ, n ≠ 0 →
      Lie.characterValue (rationalCharacters.equivCharacterLattice Z χ) x ^ n ≠ 1) :
    ∃ φ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, characterRestrict φ χ ≠ 0 := by
  have : IsAffine Z.toGrp.X.left := isAffine_of_isAffineHom Z.toGrp.X.hom
  obtain ⟨p, hp⟩ := exists_datum_of_point (rationalCharacters.equivCharacterLattice Z χ) x
  have hfin := finiteType_coordinateAlgebra Z.toGrp
  obtain ⟨Γ, hm, hΓ, p', hp'⟩ := IsDatum.exists_restrict hfin hp
  have hfg : AddGroup.FG Γ := (AddGroup.fg_iff_addSubgroup_fg Γ).mpr hΓ
  have hnt : ∀ n : ℕ, n ≠ 0 → n • (⟨_, hm⟩ : Γ) ≠ 0 := by
    intro n hn h
    apply hx n hn
    have h' := congrArg Subtype.val h
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at h'
    rw [← ofMul_pow] at h'
    exact h'
  obtain ⟨φ, hφ⟩ := exists_addMonoidHom_int_ne_zero hfg hnt
  let Φ : Γ →+ (PUnit.{u + 1} → ℤ) := AddMonoidHom.pi fun _ => φ
  have hΦ : Φ ⟨_, hm⟩ ≠ 0 := fun h => hφ (congrFun h PUnit.unit)
  obtain ⟨B, _, y, hy⟩ := (IsDatum.expMap hp' Φ).exists_finiteType hfin
  obtain ⟨L, _, _, _, z, hz⟩ := hy.exists_finiteDimensional
  obtain ⟨w, hw⟩ := IsDatum.exists_separableClosure_of_comm hz
  obtain ⟨n, hn, v, hv⟩ := hw.exists_of_isSeparable
  exact CocharacterDatum.exists_gm_characterRestrict_ne_zero
    (fun h => hΦ ((nsmul_eq_zero_iff_right hn).mp h)) hv

end Langlands.GroupScheme.CentralSurjectionImage
