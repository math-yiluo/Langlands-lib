/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Local monodromy of Frobenius-invariant torsors on curves

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k`, `z ∈ C ∖ U` and `V = U ∪ {z}`. Let `E` be an automorphism of `C` preserving `U` and fixing
`z`, semilinear over an automorphism `σ₀` of `k` with `σ₀(x) ^ Q = x`. If a `ℤ / N`-torsor `T` on
`U`, `N` invertible in `k`, is isomorphic to its transport along `E`, then `Q - 1` kills its
monodromy on the kernel of `π₁(U) → π₁(V)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.natCast_sub_one_mul_monodromy_eq_zero`).

For the geometric fibre of a curve over `𝔽_q` and a power `E = Φ ^ m` of the geometric Frobenius
fixing `z`, `Q = q ^ m`; this is the input of blueprint `proposition-no-fixed-class-degree-one--1`
used for the Frobenius-fixed systems of torsors: the residues of a Frobenius-fixed torsor lie in
`ℤ / N (-1)`, on which `Φ ^ m` acts as `Q`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open WeilGroup FiniteEtale

variable {k : Type u} [Field k] [IsAlgClosed k] {C U : Scheme.{u}} {p : C ⟶ Spec (.of k)}
  [IsCurve p] [SmoothOfRelativeDimension 1 p] [ConnectedSpace C] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

-- instance search through `SeparableClosure` and its integral closures is slow
/-- **`Q - 1` kills the local monodromy of a Frobenius-invariant torsor.** Let `E` be an
automorphism of `C`, restricting to `U`, fixing `z ∈ C ∖ U` and semilinear over an automorphism
`σ₀` of `k` with `σ₀(x) ^ Q = x`. If a `ℤ / N`-torsor `T` on `U` is isomorphic to its transport
along `E` (by `ψ`), then `(Q - 1) f_T(g) = 0` for every `g` in the kernel of
`π₁(U) → π₁(U ∪ {z})`. -/
theorem natCast_sub_one_mul_monodromy_eq_zero
    (V : C.Opens) (hV : Set.range j.base ⊆ V) (z : C)
    (hz : (V : Set C) \ Set.range j.base = {z})
    (EC : C ≅ C) (EU : U ≅ U) (hE : EU.hom ≫ j = j ≫ EC.hom) (hEz : EC.hom z = z)
    (σ₀ : k ≃+* k) (hσ₀ : EC.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k)))
    (Q : ℕ) (hQ : ∀ x : k, σ₀ x ^ Q = x)
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω') ⟶ U)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0)
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (ψ : T.P ≅ T.P)
    (hψπ : ψ.hom ≫ T.π = T.π ≫ EU.hom) (hψv : ∀ m, T.vadd m ≫ ψ.hom = ψ.hom ≫ T.vadd m)
    (g : G) (hg : g ∈ fixingSubgroup s (IsOpenImmersion.lift V.ι j
      (by rwa [Scheme.Opens.range_ι])) G) :
    ((Q : ZMod N) - 1) * (T.monodromy s G g).toAdd.down = 0 := by
  classical
  -- the curve `C` is smooth and connected, hence integral
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsRegular.of_smooth p
  have : IsIntegral C := IsRegular.isIntegral C
  obtain ⟨u₀⟩ := (inferInstance : Nonempty U)
  -- `z` is a closed boundary point and `V = U ∪ {z}`
  have hzV : z ∈ (V : Set C) \ Set.range j.base := hz ▸ rfl
  have hzj : z ∉ Set.range j.base := hzV.2
  have hzc : IsClosed ({z} : Set C) :=
    j.isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
      (IsCurve.krullDim_le_one (f := p)) ⟨_, u₀, rfl⟩ hzj
  have hVb : V = boundaryOpen (p := p) j z := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_boundaryOpen_iff]
    constructor
    · intro hx
      by_cases hxj : x ∈ Set.range j.base
      · exact Or.inl hxj
      · exact Or.inr (by simpa [hz] using (show x ∈ (V : Set C) \ Set.range j.base from ⟨hx, hxj⟩))
    · rintro (hx | rfl)
      · exact hV hx
      · exact hzV.1
  subst hVb
  -- a chart at `z` and a point `Q` over it in the integral closure in `Ω`
  obtain ⟨c⟩ := nonempty_boundaryChart (p := p) j hzj
  have := c.isMaximal_ideal
  have := isDedekindDomain_of_isAffineOpen p c.isAffineOpen
  let z' : c.W := ⟨z, c.mem⟩
  let _ : Algebra Γ(C, c.W) (C.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk C.presheaf z'
  have hloc : IsLocalization.AtPrime (C.presheaf.stalk z) c.ideal :=
    c.isAffineOpen.isLocalization_stalk z'
  -- the residue field at `z` is algebraically closed, hence perfect
  have : IsAlgClosed c.ideal.ResidueField := by
    have := Scheme.isAlgClosed_residueField_of_isClosed p z hzc
    let e₁ : Γ(C, c.W) ⧸ c.ideal ≃+* C.residueField z :=
      (IsLocalization.AtPrime.equivQuotMaximalIdeal c.ideal (C.presheaf.stalk z)).toRingEquiv
    let e₀ : Γ(C, c.W) ⧸ c.ideal ≃+* c.ideal.ResidueField :=
      RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField c.ideal)
    exact IsAlgClosed.of_ringEquiv _ _ (e₁.symm.trans e₀)
  -- the kernel of `π₁(U) → π₁(V)` is generated by inertia
  let τ : fiber (pointOfAlgebra Ω (genericPointLift j)) ≅ fiber s :=
    (nonempty_iso_of_fiberFunctor _ _).some
  let ρ := galoisToFundamentalGroup (genericPointLift j) τ G
  have hker := c.fixingSubgroup_le_topologicalClosure_normalClosure hzj c.point s G τ hg
  let φH : G →* Multiplicative (ZMod N) :=
    { toFun g := Multiplicative.ofAdd (((Q : ZMod N) - 1) * (T.monodromy s G g).toAdd.down)
      map_one' := by simp
      map_mul' g h := by
        simp only [map_mul, toAdd_mul, ULift.add_down, mul_add, ofAdd_add] }
  have hHc : IsClosed (φH.ker : Set G) := by
    have : (φH.ker : Set G) = (T.monodromy s G) ⁻¹'
        {a | ((Q : ZMod N) - 1) * a.toAdd.down = 0} := by
      ext g
      simp [φH, MonoidHom.mem_ker]
    rw [this]
    exact (isClosed_discrete _).preimage (T.monodromy s G).continuous
  suffices hsub : ((c.point.inertia Gal(Ω/C.functionField)).map ρ : Set G) ⊆ φH.ker by
    have := Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hHc hker
    simpa [φH, MonoidHom.mem_ker] using this
  rintro _ ⟨σ, hσ, rfl⟩
  change ((Q : ZMod N) - 1) * (T.monodromy s G (ρ σ)).toAdd.down = 0
  -- a primitive `N`-th root of unity of `k`, in the function field and in `Ω`
  have : NeZero (N : k) := ⟨hN⟩
  obtain ⟨ζk, hζk⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N
  set F := C.functionField
  let ι : F →+* Ω := algebraMap F Ω
  let κ : k →+* F := (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  set ζ : Ω := ι (κ ζk) with hζdef
  have hζ : IsPrimitiveRoot ζ N := hζk.map_of_injective (ι.comp κ).injective
  -- the action of `Gal(Ω / F)` on the points of `T` over the generic point
  let η : Spec (.of Ω) ⟶ U := pointOfAlgebra Ω (genericPointLift j)
  obtain ⟨t₀⟩ := T.nonempty_fiber η
  let t : Spec (.of Ω) ⟶ T.P := t₀.left
  have ht : t ≫ T.π = η := fiber_left_comp η t₀
  let χ : Gal(Ω/F) → ZMod N := fun σ ↦ (T.monodromy s G (ρ σ)).toAdd.down
  have hact (σ : Gal(Ω/F)) (t' : Spec (.of Ω) ⟶ T.P) (ht' : t' ≫ T.π = η) :
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t' = t' ≫ T.vadd ⟨χ σ⟩ :=
    specMap_comp_eq_comp_vadd_monodromy (genericPointLift j) τ G T σ t' ht'
  -- the Kummer element `x` of `T`
  obtain ⟨x, hx0, hx⟩ := T.exists_kummer_element t hζ
  have hσF (σ : Gal(Ω/F)) (f : F) : σ (ι f) = ι f := σ.commutes f
  have hχx (σ : Gal(Ω/F)) : σ x = ζ ^ (χ σ).val * x :=
    hx σ.toRingEquiv (χ σ) (hσF σ _) (hact σ t ht)
  obtain ⟨f, hf⟩ : ∃ f : F, ι f = x ^ N := by
    have hmem : x ^ N ∈ IntermediateField.fixedField
        (⊥ : IntermediateField F Ω).fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ _
      rw [map_pow, hχx, mul_pow, ← pow_mul, mul_comm (χ σ).val, pow_mul, hζ.pow_eq_one, one_pow,
        one_mul]
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact IntermediateField.mem_bot.1 hmem
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact pow_ne_zero N hx0 (by rw [← hf, map_zero])
  -- the stalk at `z` is a discrete valuation ring; `f = u π ^ a`
  have hne : c.ideal ≠ ⊥ := fun h ↦ c.ϖ_ne_zero hzj (by simpa [h] using c.ϖ_mem)
  have : IsDiscreteValuationRing (C.presheaf.stalk z) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Γ(C, c.W) hne _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk z)
  obtain ⟨u, a, hfu⟩ := IsDiscreteValuationRing.exists_eq_algebraMap_mul_zpow (F := F) hπ hf0
  have hNΩ : NeZero (N : Ω) := ⟨by
    rw [← map_natCast (ι.comp κ)]
    exact (map_ne_zero_iff _ (ι.comp κ).injective).2 hN⟩
  obtain ⟨y, hy⟩ := IsSepClosed.exists_pow_nat_eq (ι (algebraMap _ F π)) N
  have hπ0 : ι (algebraMap _ F π) ≠ 0 := (map_ne_zero_iff _ ι.injective).2
    ((map_ne_zero_iff _ (IsFractionRing.injective _ F)).2 hπ.ne_zero)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hπ0 (by rw [← hy, zero_pow (NeZero.ne N)])
  -- units at `z`
  let Us : Set Ω := {w | ∃ o : C.presheaf.stalk z, IsUnit o ∧ w = ι (algebraMap _ F o)}
  have hxy : x ^ N / (y ^ N) ^ a ∈ Us := by
    refine ⟨u, u.isUnit, ?_⟩
    rw [← hf, hfu, map_mul, map_zpow₀, hy, mul_div_assoc, div_self (zpow_ne_zero _ hπ0), mul_one]
  have hyN (σ : Gal(Ω/F)) : σ (y ^ N) = y ^ N := by rw [hy, hσF]
  -- the lift `φ` of `E` to `Ω`
  obtain ⟨φ, hφF, hφη⟩ := exists_ringEquiv_separableClosure EC Ω
  let θ := stalkAut EC hEz
  have hθ (o : C.presheaf.stalk z) :
      φ (ι (algebraMap _ F o)) = ι (algebraMap _ F (θ.hom o)) := by
    rw [hφF, functionFieldAut_algebraMap EC hEz]
  have hθ' (o : C.presheaf.stalk z) :
      φ.symm (ι (algebraMap _ F o)) = ι (algebraMap _ F (θ.inv o)) := by
    rw [RingEquiv.symm_apply_eq, hθ, ← ConcreteCategory.comp_apply, θ.inv_hom_id,
      CommRingCat.id_apply]
  have hFinv (f : F) : φ.symm (ι f) = ι ((functionFieldAut EC).inv f) := by
    rw [RingEquiv.symm_apply_eq, hφF, ← ConcreteCategory.comp_apply,
      (functionFieldAut EC).inv_hom_id, CommRingCat.id_apply]
  have hκ (b : k) : (functionFieldAut EC).hom (κ b) = κ (σ₀ b) := by
    change (functionFieldAut EC).hom (C.presheaf.germ ⊤ (genericPoint C) trivial
      (p.appTop ((Scheme.ΓSpecIso (.of k)).inv b))) = _
    rw [functionFieldAut_germ]
    change _ = C.presheaf.germ ⊤ (genericPoint C) trivial
      (p.appTop ((Scheme.ΓSpecIso (.of k)).inv (σ₀ b)))
    congr 1
    have h1 := congrArg (fun h ↦ (Scheme.Hom.appTop h).hom ((Scheme.ΓSpecIso (.of k)).inv b)) hσ₀
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
    rw [h1]
    congr 1
    exact (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ₀ : k →+* k))) b).symm
  -- `φ⁻¹` raises roots of unity to the power `Q`
  obtain ⟨cQ, hcζ, hcQ⟩ : ∃ cQ : ℕ, φ.symm ζ = ζ ^ cQ ∧ (cQ : ZMod N) = Q := by
    set b := σ₀.symm ζk
    have hb : φ.symm ζ = ι (κ b) := by
      rw [RingEquiv.symm_apply_eq, hφF, hκ, RingEquiv.apply_symm_apply]
    have hbN : b ^ N = 1 := by rw [← map_pow, hζk.pow_eq_one, map_one]
    obtain ⟨cQ, -, hc⟩ := hζk.eq_pow_of_pow_eq_one hbN
    refine ⟨cQ, by rw [hb, ← hc, map_pow, map_pow], ?_⟩
    have h := hQ b
    rw [RingEquiv.apply_symm_apply, ← hc] at h
    have := hζk.intCast_eq_of_zpow_eq (i := (cQ : ℤ)) (j := (Q : ℤ))
      (by rw [zpow_natCast, zpow_natCast, h])
    exact_mod_cast this
  -- `φ` preserves units at `z` and uniformizers
  have hφU : ∀ w ∈ Us, φ.symm w ∈ Us := by
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨θ.inv o, ho.map _, hθ' o⟩
  have hφy : φ.symm y ^ N / y ^ N ∈ Us := by
    have hirr : Irreducible (θ.inv π) :=
      (MulEquiv.irreducible_iff θ.symm.commRingCatIsoToRingEquiv.toMulEquiv).2 hπ
    obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hπ hirr
    refine ⟨v, v.isUnit, ?_⟩
    rw [← map_pow, hy, hθ', ← hv, map_mul, map_mul, mul_div_cancel_left₀ _ hπ0]
  -- the lift `φ` of `E` to the generic point of `U`
  have hηj : η ≫ j = Spec.map (CommRingCat.ofHom ι) ≫ C.fromSpecFunctionField := by
    simp only [η, pointOfAlgebra, Category.assoc, genericPointLift_comp]
    rfl
  have hyU : Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) ≫ η = η ≫ EU.hom := by
    rw [← cancel_mono j, Category.assoc, hηj, hφη, Category.assoc, hE, ← Category.assoc η, hηj,
      Category.assoc]
  -- conjugation by `φ` preserves the monodromy
  have hconj (σ : Gal(Ω/F)) : ∃ σ' : Gal(Ω/F),
      (∀ w, σ'.toRingEquiv w = φ.symm.symm (σ.toRingEquiv (φ.symm w))) ∧ χ σ' = χ σ := by
    have hfix (f : F) : (φ.symm.trans (σ.toRingEquiv.trans φ)) (algebraMap F Ω f) =
        algebraMap F Ω f := by
      change φ (σ (φ.symm (ι f))) = ι f
      rw [hFinv, hσF, ← hFinv, RingEquiv.apply_symm_apply]
    let σ' : Gal(Ω/F) := AlgEquiv.ofRingEquiv (f := φ.symm.trans (σ.toRingEquiv.trans φ)) hfix
    refine ⟨σ', fun w ↦ rfl, ?_⟩
    have h1 := hact σ' t ht
    have h2 := specMap_conj_comp_eq T EU φ hyU ψ hψπ hψv (σ := σ.toRingEquiv) (m := ⟨χ σ⟩)
      (fun t' ht' ↦ hact σ t' ht') t ht
    exact congrArg ULift.down (T.eq_of_comp_vadd_eq t (h1.symm.trans h2) default)
  -- inertia fixes the `N`-th roots of units at `z`
  let lR : k →+* Γ(C, c.W) := (C.presheaf.map (homOfLE (le_top : c.W ≤ ⊤)).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hRF (r : Γ(C, c.W)) : algebraMap Γ(C, c.W) Ω r = ι (algebraMap Γ(C, c.W) F r) :=
    IsScalarTower.algebraMap_apply _ F Ω r
  have : Nonempty c.W := ⟨z'⟩
  have := functionField_isScalarTower C c.W z'
  have hRO (r : Γ(C, c.W)) : algebraMap Γ(C, c.W) F r =
      algebraMap (C.presheaf.stalk z) F (algebraMap Γ(C, c.W) (C.presheaf.stalk z) r) :=
    IsScalarTower.algebraMap_apply _ (C.presheaf.stalk z) F r
  have hlR (b : k) : algebraMap Γ(C, c.W) Ω (lR b) = ι (κ b) := by
    rw [hRF]
    congr 1
    exact C.presheaf.germ_res_apply (homOfLE (le_top : c.W ≤ ⊤)) (genericPoint C) _ _
  have hinj : Function.Injective (algebraMap Γ(C, c.W) Ω) := by
    intro r r' h
    rw [hRF, hRF] at h
    exact (C.germToFunctionField_injective c.W) (ι.injective h)
  have hinertia : ∀ w : Ω, w ^ N ∈ Us → σ w = w := by
    rintro w ⟨o, ho, hwo⟩
    obtain ⟨⟨r, s'⟩, rfl⟩ := IsLocalization.mk'_surjective c.ideal.primeCompl o
    have hr : r ∈ c.ideal.primeCompl := (IsLocalization.AtPrime.isUnit_mk'_iff _ c.ideal r s').1 ho
    have hs : (s' : Γ(C, c.W)) ∉ c.ideal := s'.2
    have hrs : r * (s' : Γ(C, c.W)) ^ (N - 1) ∉ c.ideal := fun h ↦
      ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hr fun h' ↦ hs (Ideal.IsPrime.mem_of_pow_mem
        inferInstance _ h'))
    have hζR : IsPrimitiveRoot (algebraMap Γ(C, c.W) Ω (lR ζk)) N := by rw [hlR]; exact hζ
    have hζRu (k' : ℕ) (hk' : lR ζk ^ k' ≠ 1) : IsUnit (lR ζk ^ k' - 1) := by
      have : ζk ^ k' - 1 ≠ 0 := fun h ↦ hk' (by rw [← map_pow, sub_eq_zero.1 h, map_one])
      rw [← map_pow, ← map_one lR, ← map_sub]
      exact (Ne.isUnit this).map lR
    have := Ideal.inertia_smul_eq_of_pow_eq c.point hσ hζR hζRu (w := w)
      (r := r * (s' : Γ(C, c.W)) ^ (N - 1)) (s := s')
      (fun h ↦ hrs ((Ideal.mem_of_liesOver c.point c.ideal _).2 h))
      (fun h ↦ hs (by
        rw [show (s' : Γ(C, c.W)) = 0 from hinj (h.trans (map_zero _).symm)]
        exact c.ideal.zero_mem))
      (by
        have he (x : Γ(C, c.W)) : algebraMap Γ(C, c.W) Ω x =
            ι (algebraMap _ F (algebraMap Γ(C, c.W) (C.presheaf.stalk z) x)) := by
          rw [hRF, hRO]
        have hpow : (algebraMap Γ(C, c.W) (C.presheaf.stalk z) s') ^ N =
            algebraMap Γ(C, c.W) (C.presheaf.stalk z) s' *
              (algebraMap Γ(C, c.W) (C.presheaf.stalk z) s') ^ (N - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel NeZero.one_le]
        dsimp only at hwo
        rw [mul_pow, hwo, he, he, ← map_pow ι, ← map_mul ι, ← map_pow (algebraMap _ F),
          ← map_mul (algebraMap _ F), hpow, ← mul_assoc, IsLocalization.mk'_spec]
        simp only [map_mul, map_pow])
    exact this
  -- the tame relation
  have key := hζ.natCast_mul_eq_of_kummer (Γ := Gal(Ω/F)) AlgEquiv.toRingEquiv Us χ hx0 hy0 hxy
    hχx hyN φ.symm hcζ hφU hφy hconj hinertia
  change ((Q : ZMod N) - 1) * χ σ = 0
  rw [← hcQ, sub_mul, key, one_mul, sub_self]

end AlgebraicGeometry.Scheme.EtaleTorsor
