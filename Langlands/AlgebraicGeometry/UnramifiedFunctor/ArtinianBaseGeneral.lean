import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseDescent
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingLocus
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Jacobson.Ring

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing Polynomial

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section FG

/-- (F2): every element of `F(Spec A)`, for a `C`-algebra `A`, comes from `F(Spec C[s])` for a
finitely generated `C`-subalgebra `C[s] ⊆ A`. -/
lemma exists_fg (hZ : ZariskiSheaf F) (h2 : FilteredColimits F) {C A : Type u} [CommRing C]
    [Algebra R C] [CommRing A] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (v : F.obj (op (ovR R A))) :
    ∃ (s : Finset A) (x : F.obj (op (ovR R (Algebra.adjoin C (s : Set A))))),
      res ((Algebra.adjoin C (s : Set A)).val.restrictScalars R) x = v := by
  let h₀ : Spec (CommRingCat.of C) ⟶ Spec R := (ovR R C).hom
  let c := ChartGluing.adjoinCocone C A
  let iA : ((BaseChange.specOver h₀).obj c.pt).unop ≅ ovR R A :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [Category.id_comp, ← Spec.map_comp]
      congr 1
      ext r
      exact IsScalarTower.algebraMap_apply R C A r)
  obtain ⟨s, x, hx⟩ := ChartGluing.exists_of_isColimit (BaseChange.good_all hZ h2 h₀)
    (ChartGluing.isColimitAdjoinCocone C A) (F.map iA.hom.op v)
  let B := Algebra.adjoin C (s : Set A)
  let iB : ((BaseChange.specOver h₀).obj ((ChartGluing.adjoinDiagram C A).obj s)).unop ≅
      ovR R B :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [Category.id_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun r ↦ IsScalarTower.algebraMap_apply R C B r))
  refine ⟨s, F.map iB.inv.op x, ?_⟩
  let π := ((BaseChange.specOver h₀).map (c.ι.app s)).unop
  have e : homR (B.val.restrictScalars R) ≫ iB.inv = iA.inv ≫ π := by
    ext1
    simp [iA, iB, π, c]
    rfl
  have hx' : F.map π.op x = F.map iA.hom.op v := hx
  rw [res, ← Functor.map_comp_apply, ← op_comp, e, op_comp, Functor.map_comp_apply, hx',
    ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]

end FG

section Algebra

/-- Krull intersection and artinianity: if `1 - y` is regular on the image of `C` for every
`y ∈ 𝔮`, then `C` injects into `A₀ / 𝔮 ^ M` for some `M`. -/
lemma exists_pow_injective {C A₀ : Type*} [CommRing C] [IsArtinianRing C] [CommRing A₀]
    [IsNoetherianRing A₀] [Algebra C A₀] (𝔮 : Ideal A₀)
    (hreg : ∀ y ∈ 𝔮, ∀ c : C, (1 - y) * algebraMap C A₀ c = 0 → c = 0) :
    ∃ M : ℕ, ∀ c : C, algebraMap C A₀ c ∈ 𝔮 ^ M → c = 0 := by
  let I : ℕ → Ideal C := fun n ↦ (𝔮 ^ n).comap (algebraMap C A₀)
  have hanti : Antitone I := fun m n h ↦ Ideal.comap_mono (Ideal.pow_le_pow_right h)
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := C) (M := C)
    ⟨fun k ↦ OrderDual.toDual (I k), fun a b h ↦ OrderDual.toDual_le_toDual.mpr (hanti h)⟩
  refine ⟨n, fun c hc ↦ ?_⟩
  have hall : ∀ m, algebraMap C A₀ c ∈ 𝔮 ^ m := by
    intro m
    rcases le_total n m with h | h
    · have hIm : I n = I m := hn m h
      change c ∈ I m
      rw [← hIm]
      exact hc
    · exact Ideal.pow_le_pow_right h hc
  have hmem : algebraMap C A₀ c ∈ (⨅ i : ℕ, 𝔮 ^ i • ⊤ : Submodule A₀ A₀) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [smul_eq_mul, Ideal.mul_top]
    exact hall i
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff 𝔮 _).mp hmem
  apply hreg r hr c
  simp only [smul_eq_mul] at hrx
  rw [sub_mul, one_mul, hrx, sub_self]

/-- A local artinian `C`-algebra whose residue field is integral over `C` is integral over `C`. -/
lemma isIntegral_of_residue {C A : Type u} [CommRing C] [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] [Algebra C A] (h : Algebra.IsIntegral C (ResidueField A)) :
    Algebra.IsIntegral C A := by
  constructor
  intro x
  obtain ⟨f, hfm, hf⟩ := h.isIntegral (residue A x)
  have h1 : algebraMap A (ResidueField A) (aeval x f) = 0 := by
    rw [← Polynomial.aeval_algebraMap_apply, ResidueField.algebraMap_eq, aeval_def]
    exact hf
  have h2 : aeval x f ∈ maximalIdeal A :=
    (residue_eq_zero_iff _).mp (by rwa [ResidueField.algebraMap_eq] at h1)
  obtain ⟨n, hn⟩ := isNilpotent_of_mem_maximalIdeal h2
  exact ⟨f ^ n, hfm.pow n, by rw [← aeval_def, map_pow, hn]⟩

/-- A `C`-algebra with a map to an integral `C`-algebra whose kernel is nil is integral. -/
lemma isIntegral_of_nil_ker {C A K : Type*} [CommRing C] [CommRing A] [Algebra C A] [CommRing K]
    [Algebra C K] (φ : A →ₐ[C] K) (hker : ∀ a, φ a = 0 → IsNilpotent a)
    (h : Algebra.IsIntegral C K) : Algebra.IsIntegral C A := by
  constructor
  intro x
  obtain ⟨f, hfm, hf⟩ := h.isIntegral (φ x)
  have h1 : φ (aeval x f) = 0 := by
    rw [← Polynomial.aeval_algHom_apply, aeval_def]
    exact hf
  obtain ⟨n, hn⟩ := hker _ h1
  exact ⟨f ^ n, hfm.pow n, by rw [← aeval_def, map_pow, hn]⟩

/-- A domain `Q` embedded in a field `κ` finite over a subfield `ℓ → Q` is a field. -/
lemma isField_of_injective_finite {ℓ Q κ : Type*} [Field ℓ] [CommRing Q] [IsDomain Q] [Field κ]
    [Algebra ℓ κ] [Module.Finite ℓ κ] (ψ : Q →+* κ) (hψ : Function.Injective ψ) (μ : ℓ →+* Q)
    (h : ∀ t, ψ (μ t) = algebraMap ℓ κ t) : IsField Q := by
  let : Algebra Q κ := ψ.toAlgebra
  let : Algebra ℓ Q := μ.toAlgebra
  have : IsScalarTower ℓ Q κ := IsScalarTower.of_algebraMap_eq fun t ↦ (h t).symm
  have : Algebra.IsIntegral ℓ κ := Algebra.IsIntegral.of_finite ℓ κ
  have : Algebra.IsIntegral Q κ := Algebra.IsIntegral.tower_top ℓ
  exact isField_of_isIntegral_of_isField hψ (Field.toIsField κ)

end Algebra


section General

/-- The closed point step: if `x ∈ F(Spec A₀)` agrees with `η` at a maximal ideal `𝔮` of the
finitely generated `C`-algebra `A₀` whose residue field is integral over `C`, and `1 - y` is
regular on `C` for `y ∈ 𝔮`, then `η` lifts to `C` (`descend_finite` on `A₀ / 𝔮 ^ M`). -/
lemma descend_closed_point (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (hF : FaithfullyFlatSheaf F) (h5 : NilpotentInjective F)
    {C A₀ ℓ : Type u} [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Algebra R C]
    [CommRing A₀] [IsNoetherianRing A₀] [Algebra R A₀] [Algebra C A₀] [IsScalarTower R C A₀]
    [Algebra.FiniteType C A₀] [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ)
    (hπ : Function.Surjective π) (η : F.obj (op (ovR R ℓ))) (𝔮 : Ideal A₀) [𝔮.IsMaximal]
    (hint : Algebra.IsIntegral C (A₀ ⧸ 𝔮))
    (hreg : ∀ y ∈ 𝔮, ∀ c : C, (1 - y) * algebraMap C A₀ c = 0 → c = 0)
    (μQ : ℓ →ₐ[R] A₀ ⧸ 𝔮) (hμQ : ∀ c : C, μQ (π c) = Ideal.Quotient.mk 𝔮 (algebraMap C A₀ c))
    (x : F.obj (op (ovR R A₀))) (hx : res (Ideal.Quotient.mkₐ R 𝔮) x = res μQ η) :
    ∃ w : F.obj (op (ovR R C)), res π w = η := by
  obtain ⟨M, hM⟩ := exists_pow_injective 𝔮 hreg
  let A₃ := A₀ ⧸ 𝔮 ^ M
  have hinj₃ : Function.Injective (algebraMap C A₃) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact hM c ((Ideal.Quotient.eq_zero_iff_mem).mp hc)
  have : Nontrivial A₃ := nontrivial_of_ne (algebraMap C A₃ 0) (algebraMap C A₃ 1)
    (hinj₃.ne zero_ne_one)
  have hle : 𝔮 ^ M ≤ 𝔮 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      exfalso
      have hnt : Nontrivial (A₀ ⧸ 𝔮 ^ 0) := this
      exact Ideal.Quotient.nontrivial_iff.mp hnt (by rw [pow_zero, Ideal.one_eq_top])
    · exact Ideal.pow_le_self h.ne'
  let φ : A₃ →ₐ[R] A₀ ⧸ 𝔮 := Ideal.Quotient.factorₐ R hle
  have hφs : Function.Surjective φ := Ideal.Quotient.factor_surjective hle
  have hφnil : ∀ a : A₃, φ a = 0 → IsNilpotent a := fun a ha ↦ by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hy : y ∈ 𝔮 := (Ideal.Quotient.eq_zero_iff_mem).mp ha
    refine ⟨M, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hy M
  let : Field (A₀ ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have : IsLocalRing A₃ := isLocalRing_of_ker_nil φ.toRingHom hφs hφnil
  have : IsArtinianRing A₃ := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    have hm : maximalIdeal A₃ = RingHom.ker φ :=
      (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hφs)).symm
    refine ⟨M, ?_⟩
    rw [hm, show RingHom.ker φ = 𝔮.map (Ideal.Quotient.mk (𝔮 ^ M)) from ?_, ← Ideal.map_pow,
      Ideal.map_quotient_self, Ideal.zero_eq_bot]
    ext a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.mem_ker, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · intro h
      exact ⟨y, (Ideal.Quotient.eq_zero_iff_mem).mp h, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have := (Ideal.Quotient.eq).mp hzy
      have hy : y ∈ 𝔮 := by
        have := 𝔮.sub_mem hz (hle this)
        simpa using this
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hy
  have : Algebra.FiniteType C A₃ :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ C (𝔮 ^ M)) Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral C A₃ :=
    isIntegral_of_nil_ker (Ideal.Quotient.factorₐ C hle) hφnil hint
  have : Module.Finite C A₃ := Algebra.IsIntegral.finite
  -- the element on `A₃` lies over `η`
  let v₃ : F.obj (op (ovR R A₃)) := res (Ideal.Quotient.mkₐ R (𝔮 ^ M)) x
  have hv₃ : IsOver (IsScalarTower.toAlgHom R C A₃) π η v₃ := by
    intro K _ _ ψ ψ₀ hψ
    obtain ⟨ψ', hψ'⟩ := exists_factor φ hφs ψ (fun a ha ↦ ((hφnil a ha).map ψ).eq_zero)
    rw [← hψ', ← res_res]
    simp only [v₃, res_res]
    have e : (φ.comp (Ideal.Quotient.mkₐ R (𝔮 ^ M))) = Ideal.Quotient.mkₐ R 𝔮 := by
      ext
      rfl
    rw [e, ← res_res, hx, res_res]
    congr 1
    ext t
    obtain ⟨c, rfl⟩ := hπ t
    have h1 := congrArg (fun f ↦ f c) hψ
    simp only [AlgHom.comp_apply] at h1 ⊢
    rw [h1, hμQ, ← hψ']
    rfl
  exact descend_finite h4 hZ hF h5 hinj₃ π hπ η v₃ hv₃

lemma mem_maximalIdeal_of_isNilpotent {A : Type*} [CommRing A] [IsLocalRing A] {x : A}
    (h : IsNilpotent x) : x ∈ maximalIdeal A :=
  (mem_maximalIdeal x).mpr h.not_isUnit

/-- From agreement at the generic point of `Spec (A₀/p)` to agreement at a closed point `𝔮`
with residue field integral over `C`: (F2) spreading to a basic open `D(a)` and the
Nullstellensatz. -/
lemma closed_point_of_generic (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h2 : FilteredColimits F) {C A₀ ℓ : Type u} [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    [Algebra R C] [CommRing A₀] [Algebra R A₀] [Algebra C A₀] [IsScalarTower R C A₀]
    [Algebra.FiniteType C A₀] [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ)
    (hπ : Function.Surjective π) (η : F.obj (op (ovR R ℓ))) (p : Ideal A₀) [p.IsPrime]
    (μ : ℓ →ₐ[R] A₀ ⧸ p) (hμc : ∀ c : C, μ (π c) = Ideal.Quotient.mk p (algebraMap C A₀ c))
    (x : F.obj (op (ovR R A₀)))
    (hgen : res (IsScalarTower.toAlgHom R (A₀ ⧸ p) (FractionRing (A₀ ⧸ p)))
        (res (Ideal.Quotient.mkₐ R p) x) =
      res (IsScalarTower.toAlgHom R (A₀ ⧸ p) (FractionRing (A₀ ⧸ p))) (res μ η)) :
    ∃ (𝔮 : Ideal A₀) (_ : 𝔮.IsMaximal) (hp𝔮 : p ≤ 𝔮), Algebra.IsIntegral C (A₀ ⧸ 𝔮) ∧
      res (Ideal.Quotient.mkₐ R 𝔮) x = res ((Ideal.Quotient.factorₐ R hp𝔮).comp μ) η := by
  let D := A₀ ⧸ p
  let Kd := FractionRing D
  let xD : F.obj (op (ovR R D)) := res (Ideal.Quotient.mkₐ R p) x
  let ηD : F.obj (op (ovR R D)) := res μ η
  -- (F2): agreement on some `D[1/a]`
  obtain ⟨a, ha⟩ := Charts.exists_away_eq_of_eq (nonZeroDivisors D) Kd hZ h2 xD ηD hgen
  let Da := Localization.Away a.val
  have ha0 : a.val ≠ 0 := nonZeroDivisors.ne_zero a.2
  have : Nontrivial Da := by
    have hinjD : Function.Injective (algebraMap D Da) :=
      IsLocalization.injective Da (powers_le_nonZeroDivisors_of_noZeroDivisors ha0)
    exact nontrivial_of_ne (algebraMap D Da 0) (algebraMap D Da 1) (hinjD.ne zero_ne_one)
  -- `D` and `Da` are of finite type over `ℓ`
  let : Algebra ℓ D := μ.toRingHom.toAlgebra
  let : Algebra C ℓ := π.toRingHom.toAlgebra
  have : IsScalarTower C ℓ D := IsScalarTower.of_algebraMap_eq fun c ↦ (hμc c).symm
  have : Algebra.FiniteType C D :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ C p) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType ℓ D := Algebra.FiniteType.of_restrictScalars_finiteType C ℓ D
  have : Algebra.FinitePresentation D Da := IsLocalization.Away.finitePresentation a.val
  have : Algebra.FiniteType ℓ Da := Algebra.FiniteType.trans (S := D) inferInstance inferInstance
  -- a closed point of `D(a)`
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal Da
  have := h𝔫
  let κ := Da ⧸ 𝔫
  let : Field κ := Ideal.Quotient.field 𝔫
  have : Algebra.FiniteType ℓ κ :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℓ 𝔫) Ideal.Quotient.mk_surjective
  have : Module.Finite ℓ κ := finite_of_finite_type_of_isJacobsonRing ℓ κ
  -- the closed point `𝔮` of `Spec A₀`
  let θ : A₀ →ₐ[R] κ := (Ideal.Quotient.mkₐ R 𝔫).comp
    ((IsScalarTower.toAlgHom R D Da).comp (Ideal.Quotient.mkₐ R p))
  let θℓ : ℓ →ₐ[R] κ := (Ideal.Quotient.mkₐ R 𝔫).comp ((IsScalarTower.toAlgHom R D Da).comp μ)
  have hagree : res θ x = res θℓ η := by
    have := congrArg (res (Ideal.Quotient.mkₐ R 𝔫)) ha
    simpa only [xD, ηD, res_res] using this
  let 𝔮 : Ideal A₀ := RingHom.ker θ
  have hp𝔮 : p ≤ 𝔮 := fun y hy ↦ by
    change (Ideal.Quotient.mk 𝔫) (algebraMap D Da (Ideal.Quotient.mk p y)) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hy, map_zero, map_zero]
  let Q := A₀ ⧸ 𝔮
  let ψQ : Q →ₐ[R] κ := Ideal.Quotient.liftₐ 𝔮 θ (fun y hy ↦ hy)
  have hψQ : Function.Injective ψQ :=
    (Ideal.injective_lift_iff (I := 𝔮) (f := θ.toRingHom) (fun y hy ↦ hy)).mpr rfl
  let μQ : ℓ →ₐ[R] Q := (Ideal.Quotient.factorₐ R hp𝔮).comp μ
  have hcompQ : ∀ t : ℓ, ψQ (μQ t) = θℓ t := fun t ↦ by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (μ t)
    change ψQ (Ideal.Quotient.factor hp𝔮 (μ t)) = Ideal.Quotient.mk 𝔫 (algebraMap D Da (μ t))
    rw [← hy]
    rfl
  have hθℓ : ∀ t : ℓ, θℓ t = algebraMap ℓ κ t := fun t ↦ by
    change Ideal.Quotient.mk 𝔫 (algebraMap D Da (μ t)) = Ideal.Quotient.mk 𝔫 (algebraMap ℓ Da t)
    rw [IsScalarTower.algebraMap_apply ℓ D Da]
    rfl
  have : 𝔮.IsPrime := RingHom.ker_isPrime θ
  have : IsDomain Q := Ideal.Quotient.isDomain 𝔮
  have hQ : IsField Q := isField_of_injective_finite ψQ.toRingHom hψQ μQ.toRingHom
    (fun t ↦ (hcompQ t).trans (hθℓ t))
  have h𝔮 : 𝔮.IsMaximal := Ideal.Quotient.maximal_of_isField 𝔮 hQ
  let : Field Q := hQ.toField
  refine ⟨𝔮, h𝔮, hp𝔮, ?_, ?_⟩
  · -- `Q` embeds in `κ`, which is finite over `C`
    have : IsScalarTower C ℓ κ := IsScalarTower.of_algebraMap_eq fun c ↦ by
      change Ideal.Quotient.mk 𝔫 (algebraMap D Da (algebraMap C D c)) =
        Ideal.Quotient.mk 𝔫 (algebraMap ℓ Da (π c))
      rw [IsScalarTower.algebraMap_apply ℓ D Da]
      congr 2
      exact (hμc c).symm
    have : Module.Finite C ℓ := Module.Finite.of_surjective (Algebra.linearMap C ℓ) hπ
    have : Module.Finite C κ := Module.Finite.trans ℓ κ
    have : Algebra.IsIntegral C κ := Algebra.IsIntegral.of_finite C κ
    let ψC : Q →ₐ[C] κ :=
      { ψQ.toRingHom with
        commutes' := fun c ↦ rfl }
    exact Algebra.IsIntegral.of_injective ψC hψQ
  · apply fieldInj hF ψQ
    rw [res_res, res_res]
    have e1 : ψQ.comp (Ideal.Quotient.mkₐ R 𝔮) = θ := by
      ext
      rfl
    have e2 : ψQ.comp μQ = θℓ := AlgHom.ext hcompQ
    rw [e1, e2]
    exact hagree

/-- The descent problem for an arbitrary local artinian `A ⊇ C`: an element of `F(Spec A)` over
`η ∈ F(Spec ℓ)` gives an element of `F(Spec C)` restricting to `η`. Reduction to
`descend_finite`: by (F2) the element comes from a finitely generated `C`-subalgebra `A₀`; it
agrees with `η` at the generic point of `A₀/p`, `p = m_A ∩ A₀`, hence (F2) on a basic open
`D(a)`, hence at a closed point `𝔮` with residue field finite over `ℓ` (Nullstellensatz); by the
Krull intersection theorem `C` embeds in the local artinian `A₀/𝔮^M`, which is finite over `C`. -/
theorem descend_general (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (hF : FaithfullyFlatSheaf F) (h2 : FilteredColimits F) (h5 : NilpotentInjective F)
    {C A ℓ : Type u} [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Algebra R C]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra R A] [Algebra C A]
    [IsScalarTower R C A] (hinj : Function.Injective (algebraMap C A))
    [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ) (hπ : Function.Surjective π)
    (η : F.obj (op (ovR R ℓ))) (v : F.obj (op (ovR R A)))
    (hv : IsOver (IsScalarTower.toAlgHom R C A) π η v) :
    ∃ w : F.obj (op (ovR R C)), res π w = η := by
  classical
  have hkerπ : RingHom.ker π = maximalIdeal C :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπ)
  obtain ⟨s, x, hx⟩ := exists_fg hZ h2 (C := C) v
  let A₀ := Algebra.adjoin C (s : Set A)
  have : Algebra.FiniteType C A₀ :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  let ι₀ : A₀ →ₐ[R] A := A₀.val.restrictScalars R
  have hinj₀ : Function.Injective (algebraMap C A₀) := fun a b h ↦
    hinj (congrArg Subtype.val h)
  let ρA : A →ₐ[R] ResidueField A := IsScalarTower.toAlgHom R A (ResidueField A)
  let p : Ideal A₀ := RingHom.ker (ρA.comp ι₀)
  have hp : p.IsPrime := RingHom.ker_isPrime _
  have hmemp : ∀ y : A₀, y ∈ p ↔ (y : A) ∈ maximalIdeal A := fun y ↦ by
    change ρA (y : A) = 0 ↔ _
    exact residue_eq_zero_iff _
  have hunit : ∀ y : A₀, y ∉ p → IsUnit (y : A) := fun y hy ↦ by
    by_contra h
    exact hy ((hmemp y).mpr ((mem_maximalIdeal _).mpr h))
  -- `ℓ → A₀ / p`
  let D := A₀ ⧸ p
  obtain ⟨μ, hμ⟩ := exists_factor π hπ ((Ideal.Quotient.mkₐ R p).comp
      (IsScalarTower.toAlgHom R C A₀)) (fun c hc ↦ by
    have hcm : c ∈ maximalIdeal C := by rw [← hkerπ]; exact hc
    change Ideal.Quotient.mk p (algebraMap C A₀ c) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hmemp]
    exact mem_maximalIdeal_of_isNilpotent ((isNilpotent_of_mem_maximalIdeal hcm).map
      (algebraMap C A)))
  have hμc : ∀ c : C, μ (π c) = Ideal.Quotient.mk p (algebraMap C A₀ c) := fun c ↦
    congrArg (fun f ↦ f c) hμ
  let xD : F.obj (op (ovR R D)) := res (Ideal.Quotient.mkₐ R p) x
  let ηD : F.obj (op (ovR R D)) := res μ η
  -- `D ↪ ResidueField A` and the generic point
  let jD : D →ₐ[R] ResidueField A := Ideal.Quotient.liftₐ p (ρA.comp ι₀) (fun y hy ↦ hy)
  have hjD : Function.Injective jD :=
    (Ideal.injective_lift_iff (I := p) (f := (ρA.comp ι₀).toRingHom) (fun y hy ↦ hy)).mpr rfl
  let Kd := FractionRing D
  let jK : Kd →ₐ[R] ResidueField A := IsFractionRing.liftAlgHom (K := Kd) hjD
  have hjK : jK.comp (IsScalarTower.toAlgHom R D Kd) = jD := by
    ext y
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsFractionRing.liftAlgHom_apply,
      IsFractionRing.lift_algebraMap]
    rfl
  have hgen : res (IsScalarTower.toAlgHom R D Kd) xD =
      res (IsScalarTower.toAlgHom R D Kd) ηD := by
    apply fieldInj hF jK
    simp only [xD, ηD, res_res, ← AlgHom.comp_assoc, hjK]
    have e1 : jD.comp (Ideal.Quotient.mkₐ R p) = ρA.comp ι₀ := by
      ext
      rfl
    rw [e1, ← res_res, hx]
    refine hv _ ρA (jD.comp μ) ?_
    ext c
    change jD (μ (π c)) = ρA (algebraMap C A c)
    rw [hμc]
    rfl
  obtain ⟨𝔮, h𝔮, hp𝔮, hint, hagr⟩ := closed_point_of_generic hZ hF h2 π hπ η p μ hμc x hgen
  have hreg : ∀ y ∈ 𝔮, ∀ c : C, (1 - y) * algebraMap C A₀ c = 0 → c = 0 := by
    intro y hy c hc
    have h1 : (1 - y) ∉ p := fun h ↦ h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr (by
      have := 𝔮.add_mem (hp𝔮 h) hy
      simpa using this))
    have hu := hunit _ h1
    apply hinj
    have h0 : ((1 - y : A₀) : A) * algebraMap C A c = 0 := congrArg Subtype.val hc
    rw [map_zero]
    exact hu.mul_right_eq_zero.mp h0
  exact descend_closed_point h4 hZ hF h5 π hπ η 𝔮 hint hreg
    ((Ideal.Quotient.factorₐ R hp𝔮).comp μ) (fun c ↦ by
      change Ideal.Quotient.factor hp𝔮 (μ (π c)) = _
      rw [hμc]
      rfl) x hagr

end General

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
