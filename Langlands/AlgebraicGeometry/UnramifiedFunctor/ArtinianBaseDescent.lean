import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseFlat
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalProperties.Basic

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Normal

/-- In a field `κ` receiving compatible maps from an algebraic extension `K` of `ℓ` and from a
normal extension `N` of `ℓ` into which `K` embeds, the image of `K` lies in the image of `N`:
every element of `K` maps to a root of its minimal polynomial, which splits over `N`. -/
lemma range_le_of_normal {ℓ K N κ : Type*} [Field ℓ] [Field K] [Field N] [Field κ]
    [Algebra ℓ K] [Algebra ℓ N] [Algebra.IsAlgebraic ℓ K] [Normal ℓ N] (σ : K →ₐ[ℓ] N)
    (α : K →+* κ) (β : N →+* κ) (h : α.comp (algebraMap ℓ K) = β.comp (algebraMap ℓ N))
    (x : K) : α x ∈ β.range := by
  have hx : IsIntegral ℓ (σ x) := (Algebra.IsIntegral.isIntegral x).map σ
  have hsplit := Normal.splits (inferInstance : Normal ℓ N) (σ x)
  have hne : (minpoly ℓ (σ x)).map (algebraMap ℓ N) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hx)
  refine hsplit.mem_range_of_isRoot hne ?_
  rw [Polynomial.map_map, ← h, ← Polynomial.map_map, minpoly.algHom_eq σ σ.injective,
    IsRoot, eval_map, Polynomial.eval₂_hom, eval_map, ← aeval_def, minpoly.aeval, map_zero]

end Normal


section Factors

/-- Descent to the image of `P` in a local factor `T_𝔪` of an artinian `P`-algebra `T`, when
the residue field of `T_𝔪` is reached from `P` (same residue field case, `descend_local`). -/
lemma lift_quotient_localization (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (h5 : NilpotentInjective F) {P T ℓ' : Type u} [CommRing P] [IsLocalRing P]
    [IsArtinianRing P] [Algebra R P] [CommRing T] [Algebra R T] [Algebra P T]
    [IsScalarTower R P T] [Module.Finite P T] [IsArtinianRing T] [Field ℓ'] [Algebra R ℓ']
    (πP : P →ₐ[R] ℓ') (hπP : Function.Surjective πP) (η' : F.obj (op (ovR R ℓ')))
    (vT : F.obj (op (ovR R T))) (hv : IsOver (IsScalarTower.toAlgHom R P T) πP η' vT)
    (𝔪 : Ideal T) [𝔪.IsMaximal]
    (hres : Function.Surjective
      ((residue (Localization.AtPrime 𝔪)).comp (algebraMap P (Localization.AtPrime 𝔪)))) :
    ∃ w : F.obj (op (ovR R (P ⧸ RingHom.ker (algebraMap P (Localization.AtPrime 𝔪))))),
      IsOver (Ideal.Quotient.mkₐ R (RingHom.ker (algebraMap P (Localization.AtPrime 𝔪))))
        πP η' w := by
  let L := Localization.AtPrime 𝔪
  let k := RingHom.ker (algebraMap P L)
  have hkerπ : RingHom.ker πP = maximalIdeal P :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπP)
  have hk : k ≤ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top _)
  have hknil : IsNilpotent k := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal P).mp inferInstance
    exact ⟨n, le_bot_iff.mp ((Ideal.pow_right_mono hk n).trans (by rw [hn]; rfl))⟩
  let Q := P ⧸ k
  have : IsLocalRing Q := Charts.isLocalRing_quotient hknil
  let : Algebra Q L := (Ideal.Quotient.lift k (algebraMap P L) (fun a ha ↦ ha)).toAlgebra
  have : IsScalarTower R Q L := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R L r = algebraMap P L (algebraMap R P r)
    exact IsScalarTower.algebraMap_apply R P L r
  have : IsScalarTower P Q L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hinj : Function.Injective (algebraMap Q L) :=
    (Ideal.injective_lift_iff (fun a ha ↦ ha)).mpr rfl
  have : Module.Finite P L := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom P T L).toLinearMap
    (IsArtinianRing.localization_surjective 𝔪.primeCompl L)
  have : Module.Finite Q L := Module.Finite.of_restrictScalars_finite P Q L
  obtain ⟨πQ, hπQ⟩ := exists_factor (Ideal.Quotient.mkₐ R k) Ideal.Quotient.mk_surjective πP
    (fun a ha ↦ by
      rw [← RingHom.mem_ker, hkerπ]
      exact hk ((Ideal.Quotient.eq_zero_iff_mem).mp ha))
  have hπQs : Function.Surjective πQ := fun z ↦ by
    obtain ⟨p, rfl⟩ := hπP z
    exact ⟨Ideal.Quotient.mk _ p, congrArg (fun f ↦ f p) hπQ⟩
  let vL : F.obj (op (ovR R L)) := res (IsScalarTower.toAlgHom R T L) vT
  have hvL : IsOver (IsScalarTower.toAlgHom R Q L) πQ η' vL := by
    intro K _ _ ψ ψ₀ hψ
    rw [res_res]
    refine hv K _ ψ₀ ?_
    ext p
    have h1 := congrArg (fun f ↦ f (Ideal.Quotient.mk k p)) hψ
    have h2 := congrArg (fun f ↦ f p) hπQ
    simp only [AlgHom.comp_apply] at h1 h2 ⊢
    rw [← h2]
    refine h1.trans ?_
    change ψ (algebraMap P L p) = ψ (algebraMap T L (algebraMap P T p))
    rw [← IsScalarTower.algebraMap_apply]
  have hloc : ∀ c ∈ maximalIdeal Q, algebraMap Q L c ∈ maximalIdeal L := fun c hc ↦ by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ ((isNilpotent_of_mem_maximalIdeal hc).map (algebraMap Q L)).not_isUnit hu
  have hres' : Function.Surjective ((residue L).comp (algebraMap Q L)) := fun z ↦ by
    obtain ⟨p, hp⟩ := hres z
    exact ⟨Ideal.Quotient.mk k p, hp⟩
  obtain ⟨w, hw⟩ := descend_local h4 hZ h5 hinj hloc hres' πQ hπQs η' vL hvL
  refine ⟨w, ?_⟩
  have := isOver_of_surjective (Ideal.Quotient.mkₐ R k) Ideal.Quotient.mk_surjective πQ hw
  rwa [hπQ] at this

/-- If `η'` lifts to every `P/kᵢ` for a nonempty finite family of ideals with `⋂ kᵢ = 0`, it lifts
to `P` (iterate `inter_closed`). -/
lemma lift_of_iInf (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F) (h5 : NilpotentInjective F)
    {P ℓ' : Type u} [CommRing P] [IsLocalRing P] [IsArtinianRing P] [Algebra R P] [Field ℓ']
    [Algebra R ℓ'] (πP : P →ₐ[R] ℓ') (hπP : Function.Surjective πP) (η' : F.obj (op (ovR R ℓ')))
    {ι : Type*} [Fintype ι] [Nonempty ι] (k : ι → Ideal P)
    (hk : ∀ i, ∃ w : F.obj (op (ovR R (P ⧸ k i))), IsOver (Ideal.Quotient.mkₐ R (k i)) πP η' w)
    (hbot : ⨅ i, k i = ⊥) : ∃ w : F.obj (op (ovR R P)), res πP w = η' := by
  have key : ∀ s : Finset ι, s.Nonempty → ∃ w : F.obj (op (ovR R (P ⧸ s.inf k))),
      IsOver (Ideal.Quotient.mkₐ R (s.inf k)) πP η' w := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      rw [Finset.inf_singleton]
      exact hk a
    | cons a s ha hs ih =>
      rw [Finset.inf_cons]
      exact inter_closed h4 hZ h5 πP hπP η' _ _ (hk a) ih
  obtain ⟨w, hw⟩ := key Finset.univ Finset.univ_nonempty
  have hb : Finset.univ.inf k = ⊥ := by rw [← hbot, Finset.inf_univ_eq_iInf]
  have hbij : Function.Bijective (Ideal.Quotient.mkₐ R (Finset.univ.inf k)) :=
    ⟨fun a b h ↦ by
      have := (Ideal.Quotient.eq).mp h
      rw [hb, Ideal.mem_bot, sub_eq_zero] at this
      exact this, Ideal.Quotient.mk_surjective⟩
  let e : (P ⧸ Finset.univ.inf k) ≃ₐ[R] P := (AlgEquiv.ofBijective _ hbij).symm
  refine ⟨res e.toAlgHom w, IsOver.res_eq ?_⟩
  have h := hw.restrict e.toAlgHom
  have he : e.toAlgHom.comp (Ideal.Quotient.mkₐ R (Finset.univ.inf k)) = AlgHom.id R P := by
    ext p
    exact (AlgEquiv.ofBijective _ hbij).symm_apply_apply p
  rwa [he] at h

open Algebra.TensorProduct in
/-- Faithfully flat descent of a lift: an element of `F(Spec P)` over `η|_N`, for a faithfully
flat finite `C → P` with compatible residue maps, comes from an element of `F(Spec C)` over `η`. -/
lemma descend_flat (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h5 : NilpotentInjective F) {C P ℓ N : Type u} [CommRing C] [Algebra R C] [CommRing P]
    [IsLocalRing P] [IsArtinianRing P] [Algebra R P] [Algebra C P] [IsScalarTower R C P]
    [Module.FaithfullyFlat C P] [Module.Finite C P] [Field ℓ] [Algebra R ℓ] [Field N]
    [Algebra R N] [Algebra ℓ N] [IsScalarTower R ℓ N] (π : C →ₐ[R] ℓ)
    (hπ : Function.Surjective π) (πP : P →ₐ[R] N) (hπP : Function.Surjective πP)
    (hcomp : πP.comp (IsScalarTower.toAlgHom R C P) = (IsScalarTower.toAlgHom R ℓ N).comp π)
    (η : F.obj (op (ovR R ℓ))) (wP : F.obj (op (ovR R P)))
    (hwP : res πP wP = res (IsScalarTower.toAlgHom R ℓ N) η) :
    ∃ w₀ : F.obj (op (ovR R C)), res π w₀ = η := by
  have : IsArtinianRing (P ⊗[C] P) := IsArtinianRing.of_finite P (P ⊗[C] P)
  have hkerπP : RingHom.ker πP = maximalIdeal P :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπP)
  have hfac : ∀ {K : Type u} [Field K] [Algebra R K] (φ : P →ₐ[R] K),
      ∃ φ' : N →ₐ[R] K, φ'.comp πP = φ := fun φ ↦
    exists_factor πP hπP φ (fun a ha ↦ map_maximalIdeal_eq_zero φ.toRingHom
      (by rw [← hkerπP]; exact ha))
  let ι := IsScalarTower.toAlgHom R ℓ N
  have hcompat : res (includeLeft (R := C) (S := R) (A := P) (B := P)) wP =
      res ((includeRight (R := C) (A := P) (B := P)).restrictScalars R) wP := by
    refine eq_of_fieldAgree hZ h5 fun K _ _ ψ ↦ ?_
    obtain ⟨ψ₁, hψ₁⟩ := hfac (ψ.comp (includeLeft (R := C) (S := R) (A := P) (B := P)))
    obtain ⟨ψ₂, hψ₂⟩ := hfac (ψ.comp ((includeRight (R := C) (A := P) (B := P)).restrictScalars R))
    rw [res_res, res_res, ← hψ₁, ← hψ₂, ← res_res, ← res_res, hwP, res_res, res_res]
    congr 1
    ext x
    obtain ⟨c, rfl⟩ := hπ x
    have h0 := congrArg (fun f ↦ f c) hcomp
    have h1 := congrArg (fun f ↦ f (algebraMap C P c)) hψ₁
    have h2 := congrArg (fun f ↦ f (algebraMap C P c)) hψ₂
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h0 h1 h2 ⊢
    change ψ₁ (ι (π c)) = ψ₂ (ι (π c))
    simp only [ι, IsScalarTower.coe_toAlgHom']
    rw [← h0, h1, h2]
    congr 1
    simp only [includeLeft_apply, AlgHom.coe_restrictScalars', includeRight_apply]
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨w₀, hw₀⟩ := flatDescent hF C P wP hcompat
  refine ⟨w₀, fieldInj hF ι ?_⟩
  rw [res_res, ← hcomp, ← res_res, hw₀, hwP]

end Factors


section Finite

open Algebra.TensorProduct

/-- The descent problem with a finite residue field extension. Let `C → A` be an injective
finite map of local artinian rings and `π : C → ℓ` a residue map. An element of `F(Spec A)`
over `η ∈ F(Spec ℓ)` gives an element of `F(Spec C)` restricting to `η`. The residue field `K`
of `A` is embedded in a finite normal extension `N` of `ℓ`; `P` is a finite free local
`C`-algebra with residue field `N` (`flatExt`); the residue fields of the local factors of
`P ⊗_C A` are reached from `P` (`range_le_of_normal`), so `descend_local` lifts `η|_N` to the
image of `P` in each factor, `lift_of_iInf` lifts it to `P`, and `descend_flat` descends. -/
theorem descend_finite (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F)
    (hF : FaithfullyFlatSheaf F) (h5 : NilpotentInjective F)
    {C A ℓ : Type u} [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Algebra R C]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra R A] [Algebra C A]
    [IsScalarTower R C A] [Module.Finite C A] (hinj : Function.Injective (algebraMap C A))
    [Field ℓ] [Algebra R ℓ] (π : C →ₐ[R] ℓ) (hπ : Function.Surjective π)
    (η : F.obj (op (ovR R ℓ))) (v : F.obj (op (ovR R A)))
    (hv : IsOver (IsScalarTower.toAlgHom R C A) π η v) :
    ∃ w : F.obj (op (ovR R C)), res π w = η := by
  classical
  have hkerπ : RingHom.ker π = maximalIdeal C :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπ)
  -- the residue field `K` of `A` over `ℓ`
  let K := ResidueField A
  let ρA : A →ₐ[R] K := IsScalarTower.toAlgHom R A K
  obtain ⟨lam, hlam⟩ := exists_factor π hπ (ρA.comp (IsScalarTower.toAlgHom R C A))
    (fun c hc ↦ map_maximalIdeal_eq_zero (ρA.comp (IsScalarTower.toAlgHom R C A)).toRingHom
      (by rw [← hkerπ]; exact hc))
  let : Algebra ℓ K := lam.toRingHom.toAlgebra
  have : IsScalarTower R ℓ K := IsScalarTower.of_algebraMap_eq fun r ↦ (lam.commutes r).symm
  let : Algebra C ℓ := π.toRingHom.toAlgebra
  have : IsScalarTower C ℓ K := IsScalarTower.of_algebraMap_eq fun c ↦
    (congrArg (fun f ↦ f c) hlam).symm
  have : Module.Finite C K := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom C A K).toLinearMap (IsLocalRing.residue_surjective)
  have : FiniteDimensional ℓ K := Module.Finite.of_restrictScalars_finite C ℓ K
  -- a finite normal extension `N` of `ℓ` containing `K`
  have : Algebra.IsAlgebraic ℓ K := Algebra.IsAlgebraic.of_finite ℓ K
  let σ₀ : K →ₐ[ℓ] AlgebraicClosure ℓ := IsAlgClosed.lift
  let N := IntermediateField.normalClosure ℓ K (AlgebraicClosure ℓ)
  let σ : K →ₐ[ℓ] N := (normalClosure.algHomEquiv ℓ K (AlgebraicClosure ℓ)).symm σ₀
  have : FiniteDimensional ℓ N := inferInstance
  have : Normal ℓ N := inferInstance
  let : Algebra R N := ((algebraMap ℓ N).comp (algebraMap R ℓ)).toAlgebra
  have : IsScalarTower R ℓ N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ι : ℓ →ₐ[R] N := IsScalarTower.toAlgHom R ℓ N
  -- the flat extension `P` with residue field `N`
  obtain ⟨P, _, _, _, _, hPl, hPa, hPfree, hPfin, πP, hπPs, hπP⟩ :=
    flatExt (R := R) (Module.finrank ℓ N) C ℓ N π hπ le_rfl
  have : IsLocalHom (algebraMap C P) := ⟨fun c hc ↦ by
    by_contra hcu
    have hcm : c ∈ maximalIdeal C := (mem_maximalIdeal c).mpr hcu
    exact ((isNilpotent_of_mem_maximalIdeal hcm).map (algebraMap C P)).not_isUnit hc⟩
  have : Module.FaithfullyFlat C P := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let η' : F.obj (op (ovR R N)) := res ι η
  -- `T = P ⊗_C A`
  let T := P ⊗[C] A
  have : IsArtinianRing T := IsArtinianRing.of_finite P T
  let iP : P →ₐ[R] T := IsScalarTower.toAlgHom R P T
  let iA : A →ₐ[R] T := (includeRight (R := C) (A := P) (B := A)).restrictScalars R
  have hiPA : ∀ c : C, iP (algebraMap C P c) = iA (algebraMap C A c) := fun c ↦ by
    simp only [iP, iA, IsScalarTower.coe_toAlgHom', AlgHom.coe_restrictScalars',
      includeRight_apply]
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hiPinj : Function.Injective iP := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := P)
      (Algebra.linearMap C A) hinj
    intro x y hxy
    apply (TensorProduct.rid C P).symm.injective
    apply h
    simp only [TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
      map_one]
    exact hxy
  -- `res iA v` lies over `η'`
  let vT : F.obj (op (ovR R T)) := res iA v
  have hvT : IsOver (IsScalarTower.toAlgHom R P T) πP η' vT := by
    intro K' _ _ ψ ψ₀ hψ
    simp only [vT, η', res_res]
    refine hv K' (ψ.comp iA) (ψ₀.comp ι) ?_
    ext c
    have h1 := congrArg (fun f ↦ f c) hπP
    have h2 := congrArg (fun f ↦ f (algebraMap C P c)) hψ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2 ⊢
    change ψ₀ (ι (π c)) = ψ (iA (algebraMap C A c))
    rw [← hiPA]
    change ψ₀ (algebraMap ℓ N (π c)) = ψ (algebraMap P T (algebraMap C P c))
    rw [← h1]
    exact h2
  have hkerπP : RingHom.ker πP = maximalIdeal P :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπPs)
  -- the residue fields of the local factors of `T` are reached from `P`
  have hres : ∀ 𝔪 : MaximalSpectrum T, Function.Surjective
      ((residue (Localization.AtPrime 𝔪.asIdeal)).comp
        (algebraMap P (Localization.AtPrime 𝔪.asIdeal))) := by
    intro 𝔪
    let L := Localization.AtPrime 𝔪.asIdeal
    let κ := ResidueField L
    let τ : T →ₐ[R] κ := (IsScalarTower.toAlgHom R L κ).comp (IsScalarTower.toAlgHom R T L)
    let β : P →ₐ[R] κ := τ.comp iP
    let α : A →ₐ[R] κ := τ.comp iA
    obtain ⟨βb, hβb⟩ := exists_factor πP hπPs β (fun a ha ↦
      map_maximalIdeal_eq_zero β.toRingHom (by rw [← hkerπP]; exact ha))
    obtain ⟨αb, hαb⟩ := exists_factor ρA IsLocalRing.residue_surjective α (fun a ha ↦
      map_maximalIdeal_eq_zero α.toRingHom ((residue_eq_zero_iff a).mp ha))
    have hcompat : αb.toRingHom.comp (algebraMap ℓ K) = βb.toRingHom.comp (algebraMap ℓ N) := by
      ext x
      obtain ⟨c, rfl⟩ := hπ x
      have h1 := congrArg (fun f ↦ f c) hlam
      have h2 := congrArg (fun f ↦ f c) hπP
      have h3 := congrArg (fun f ↦ f (algebraMap C A c)) hαb
      have h4' := congrArg (fun f ↦ f (algebraMap C P c)) hβb
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at h1 h2 h3 h4'
      change αb (lam (π c)) = βb (algebraMap ℓ N (π c))
      rw [h1, ← h2]
      rw [h3, h4']
      simp only [α, β, AlgHom.comp_apply, hiPA]
    have hmem : ∀ a : A, ∃ p : P, α a = β p := fun a ↦ by
      obtain ⟨n, hn⟩ := range_le_of_normal σ αb.toRingHom βb.toRingHom hcompat (ρA a)
      obtain ⟨p, rfl⟩ := hπPs n
      refine ⟨p, ?_⟩
      have h1 := congrArg (fun f ↦ f a) hαb
      have h2 := congrArg (fun f ↦ f p) hβb
      simp only [AlgHom.comp_apply] at h1 h2
      rw [← h1, ← h2]
      exact hn.symm
    have hT : ∀ t : T, ∃ p : P, τ t = β p := fun t ↦ by
      induction t using TensorProduct.inductionOn with
      | tmul p a =>
        obtain ⟨p', hp'⟩ := hmem a
        refine ⟨p * p', ?_⟩
        have : (p ⊗ₜ[C] a : T) = iP p * iA a := by
          simp only [iP, iA, IsScalarTower.coe_toAlgHom', AlgHom.coe_restrictScalars',
            includeRight_apply]
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this, map_mul, map_mul]
        exact congrArg (τ (iP p) * ·) hp'
      | add x y hx hy =>
        obtain ⟨p₁, h₁⟩ := hx
        obtain ⟨p₂, h₂⟩ := hy
        exact ⟨p₁ + p₂, by rw [map_add, map_add, h₁, h₂]⟩
    intro z
    obtain ⟨l, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨t, rfl⟩ := IsArtinianRing.localization_surjective 𝔪.asIdeal.primeCompl L l
    obtain ⟨p, hp⟩ := hT t
    refine ⟨p, ?_⟩
    have : algebraMap P L p = algebraMap T L (iP p) := IsScalarTower.algebraMap_apply P T L p
    simp only [RingHom.comp_apply]
    rw [this]
    exact hp.symm
  have hlift : ∀ 𝔪 : MaximalSpectrum T, ∃ w : F.obj (op (ovR R
      (P ⧸ RingHom.ker (algebraMap P (Localization.AtPrime 𝔪.asIdeal))))),
      IsOver (Ideal.Quotient.mkₐ R (RingHom.ker (algebraMap P (Localization.AtPrime 𝔪.asIdeal))))
        πP η' w := fun 𝔪 ↦ by
    have := 𝔪.isMaximal
    exact lift_quotient_localization h4 hZ h5 πP hπPs η' vT hvT 𝔪.asIdeal (hres 𝔪)
  have hbot : ⨅ 𝔪 : MaximalSpectrum T,
      RingHom.ker (algebraMap P (Localization.AtPrime 𝔪.asIdeal)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_iInf] at hx
    have h0 : iP x = 0 := by
      have := Ideal.mem_of_localization_maximal (J := (⊥ : Ideal T)) (r := iP x)
        (fun 𝔫 h𝔫 ↦ by
          have hx' := hx ⟨𝔫, h𝔫⟩
          rw [RingHom.mem_ker] at hx'
          rw [Ideal.map_bot, Ideal.mem_bot]
          change algebraMap T _ (algebraMap P T x) = 0
          rw [← IsScalarTower.algebraMap_apply]
          exact hx')
      exact (Ideal.mem_bot).mp this
    exact (Ideal.mem_bot).mpr (hiPinj (by rw [h0, map_zero]))
  have : Nontrivial T := nontrivial_of_ne (iP 0) (iP 1) (hiPinj.ne zero_ne_one)
  have : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  have : Nonempty (MaximalSpectrum T) :=
    ⟨⟨_, (Ideal.exists_maximal T).choose_spec⟩⟩
  obtain ⟨wP, hwP⟩ := lift_of_iInf h4 hZ h5 πP hπPs η' _ hlift hbot
  exact descend_flat hZ hF h5 π hπ πP hπPs hπP η wP hwP

end Finite

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
