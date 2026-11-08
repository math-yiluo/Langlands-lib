import Langlands.ClassField.Global.IdeleLocalInjectivity
import Langlands.ClassField.Global.RelativeWeilLocalCosets
import Langlands.ClassField.Global.RelativeWeilTransfer
import Langlands.GroupTheory.TransferDoubleCoset
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement

/-!
# The transfer of the local maps `W_{K_u} → W_{E/K}`

Double-coset data for the transfer `W_{E/K} → C_E` restricted to the image of
`localPlaceMap u`, indexed by the places of `E` above `u`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

universe u

section Upper

attribute [local instance] relativeGaloisTopology

variable (c : FundamentalClass.ClassFamily.{u}) {F E : Type u}
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  (K : Type u) [Field K] [NumberField K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
  [IsGalois K E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal] (u : FinitePlacesAbove K z)

include c in
omit [IsGalois K E] in
theorem completionClosureEmbedding_mem_range (a : u.1.adicCompletion K) :
    completionClosureEmbedding z u.1 a ∈ (placeClosureAlgHom z ⟨w, ‹_›⟩).range := by
  have hS := subalgebra_eq_top_of_algebraMap_mem z u.1
    ((placeClosureAlgHom z ⟨w, ‹_›⟩).range.comap (placeClosureAlgHom z u)) (fun k => by
      refine ⟨algebraMap E (w.adicCompletion E)
        ((projection c F E (placeRepresentative c K z w u))⁻¹ (algebraMap K E k)), ?_⟩
      exact (cosetEmbedding_placeRepresentative c K z w u k))
  have ha : a ∈ (placeClosureAlgHom z ⟨w, ‹_›⟩).range.comap (placeClosureAlgHom z u) :=
    hS ▸ Algebra.mem_top
  exact ha

include c in
omit [IsGalois K E] in
/-- The embedding `K_u → E_w` over `F_z` through which `K_u` and `E_w` have compatible
closure embeddings: `completionClosureEmbedding z w ∘ twistedMap = completionClosureEmbedding z u`. -/
def twistedMap :
    u.1.adicCompletion K →ₐ[z.adicCompletion F] w.adicCompletion E :=
  (AlgEquiv.ofInjectiveField (placeClosureAlgHom z ⟨w, ‹_›⟩)).symm.toAlgHom.comp
    ((placeClosureAlgHom z u).codRestrict _
      (completionClosureEmbedding_mem_range c K z w u))

omit [IsGalois K E] in
theorem completionClosureEmbedding_twistedMap (a : u.1.adicCompletion K) :
    completionClosureEmbedding z w (twistedMap c K z w u a) = completionClosureEmbedding z u.1 a :=
  congrArg Subtype.val ((AlgEquiv.ofInjectiveField (placeClosureAlgHom z ⟨w, ‹_›⟩)).apply_symm_apply
    ((placeClosureAlgHom z u).codRestrict _ (completionClosureEmbedding_mem_range c K z w u) a))

omit [IsGalois K E] in
theorem twistedMap_algebraMap (k : K) :
    twistedMap c K z w u (algebraMap K (u.1.adicCompletion K) k) =
      algebraMap E (w.adicCompletion E)
        ((projection c F E (placeRepresentative c K z w u))⁻¹ (algebraMap K E k)) := by
  apply (completionClosureEmbedding z w).injective
  rw [completionClosureEmbedding_twistedMap]
  exact (cosetEmbedding_placeRepresentative c K z w u k).symm

omit [IsGalois F E] [IsGalois K E] [w.asIdeal.LiesOver z.asIdeal] in
/-- Transport of a local unit along a field automorphism `ρ` of `E` over `F` and an embedding
`g' : K_u → E_q` compatible with `ρ⁻¹` on `K`, where `q` is the pullback of `v`: the result is
the image of the unit under the completion map `K_u → E_v`. -/
theorem ideleClassEquiv_ofAdicCompletion_units_map (ρ : E ≃ₐ[F] E) (v : FinitePlacesAbove E u.1)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) [q.asIdeal.LiesOver z.asIdeal]
    (hq : finitePlaceEquiv ρ.toRingEquiv v.1 = q)
    (g' : u.1.adicCompletion K →ₐ[z.adicCompletion F] q.adicCompletion E)
    (hg' : ∀ k : K, g' (algebraMap K (u.1.adicCompletion K) k) =
      algebraMap E (q.adicCompletion E) (ρ.symm (algebraMap K E k)))
    (a : (u.1.adicCompletion K)ˣ) :
    ideleClassEquiv ρ.toRingEquiv (IdeleClassGroup.ofAdicCompletion (𝓞 E) E q
        (Units.map g'.toRingHom.toMonoidHom a)) =
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E v.1
        (Units.map (FiniteExtension.completionMap u.1 v.1).toMonoidHom a) := by
  subst hq
  have hvz : v.1.asIdeal.LiesOver z.asIdeal :=
    Ideal.LiesOver.trans v.1.asIdeal u.1.asIdeal z.asIdeal
  rw [ideleClassEquiv_ofAdicCompletion]
  congr 1
  apply Units.ext
  change finiteCompletionEquiv ρ.toRingEquiv v.1 (g' a) = FiniteExtension.completionMap u.1 v.1 a
  let φ := finiteCompletionEquiv ρ.toRingEquiv v.1
  have hφz : ∀ b : z.adicCompletion F, φ (FiniteExtension.completionMap z
      (finitePlaceEquiv ρ.toRingEquiv v.1) b) = FiniteExtension.completionMap z v.1 b := by
    have h1 : Continuous (fun b => φ (FiniteExtension.completionMap z
        (finitePlaceEquiv ρ.toRingEquiv v.1) b)) :=
      (continuous_finiteCompletionEquiv _ _).comp (FiniteExtension.continuous_completionMap _ _)
    have heq := (z.denseRange_algebraMap F).equalizer h1
      (FiniteExtension.continuous_completionMap z v.1) (funext fun b => by
        simp only [Function.comp_apply, FiniteExtension.completionMap_coe]
        rw [finiteCompletionEquiv_coe]
        congr 1
        exact ρ.commutes b)
    exact fun b => congrFun heq b
  let f₁ : u.1.adicCompletion K →ₐ[z.adicCompletion F] v.1.adicCompletion E :=
    { (φ.toRingHom.comp g'.toRingHom) with
      commutes' := fun b => by
        change φ (g' (algebraMap _ _ b)) = _
        rw [AlgHom.commutes]
        exact hφz b }
  let f₂ : u.1.adicCompletion K →ₐ[z.adicCompletion F] v.1.adicCompletion E :=
    { FiniteExtension.completionMap u.1 v.1 with
      commutes' := fun b => by
        change FiniteExtension.completionMap u.1 v.1 (FiniteExtension.completionMap z u.1 b) =
          FiniteExtension.completionMap z v.1 b
        rw [← ClassField.Global.CompletionTower.completionMap_comp z u.1 v.1]
        rfl }
  have hS := subalgebra_eq_top_of_algebraMap_mem z u.1 (AlgHom.equalizer f₁ f₂) (fun k => by
    change φ (g' (algebraMap K _ k)) = FiniteExtension.completionMap u.1 v.1 (algebraMap K _ k)
    rw [hg', finiteCompletionEquiv_coe, FiniteExtension.completionMap_coe]
    congr 1
    exact ρ.apply_symm_apply _)
  have ha : (a : u.1.adicCompletion K) ∈ AlgHom.equalizer f₁ f₂ := hS ▸ Algebra.mem_top
  exact ha

/-- The lift `\bar{F_z} → \bar{K_u}` of the closure along `F_z → K_u`. -/
abbrev closureLift :
    AlgebraicClosure (z.adicCompletion F) →+* AlgebraicClosure (u.1.adicCompletion K) :=
  Weil.Local.extensionClosureLift (padicField z) (towerPadicField z u.1)
    (completionPadicAlgHom z u.1)

/-- The Galois image of `W_{K_u}`, typed in the absolute Galois group of the completion
`u.adicCompletion K` itself. -/
def localGaloisImage (ℓ : Weil.Local.localWeilGroup (towerPadicField z u.1)) :
    Field.absoluteGaloisGroup (u.1.adicCompletion K) :=
  Weil.Local.localProjection (towerPadicField z u.1) ℓ

theorem localGaloisImage_denseRange : DenseRange (localGaloisImage K z u) :=
  Weil.Local.localProjection_denseRange (towerPadicField z u.1)

/-- For `x ∈ W_{E/F}` and `g ∈ W_{E/K}`, the embedding
`y ↦ λ(j_w((projection x)⁻¹ (projection g y)))` of `E` into `\bar{K_u}`. -/
def upperEmbedding (x : RelativeWeilGroup c F E) (g : RelativeWeilGroup c K E) :
    E →+* AlgebraicClosure (u.1.adicCompletion K) :=
  (closureLift K z u).comp ((closurePlaceEmbedding z w).comp
    (((projection c F E x)⁻¹.toAlgHom.toRingHom).comp
      (projection c K E g).toAlgHom.toRingHom))

omit [IsScalarTower F K E] in
theorem upperEmbedding_apply (x : RelativeWeilGroup c F E) (g : RelativeWeilGroup c K E)
    (y : E) :
    upperEmbedding c K z w u x g y =
      closureLift K z u (closurePlaceEmbedding z w
        ((projection c F E x)⁻¹ (projection c K E g y))) :=
  rfl

omit [IsScalarTower F K E] in
theorem upperEmbedding_algebraMap (x : RelativeWeilGroup c F E)
    (hx : ∀ k : K, cosetEmbedding c K z w x k = placeEmbedding z u k)
    (g : RelativeWeilGroup c K E) (k : K) :
    upperEmbedding c K z w u x g (algebraMap K E k) =
      algebraMap (u.1.adicCompletion K) (AlgebraicClosure (u.1.adicCompletion K))
        (algebraMap K (u.1.adicCompletion K) k) := by
  rw [upperEmbedding_apply, AlgEquiv.commutes]
  change closureLift K z u (cosetEmbedding c K z w x k) = _
  rw [hx]
  exact Weil.Local.extensionClosureLift_fieldEmbedding _ _ _ _

omit [IsScalarTower F K E] in
theorem upperEmbedding_eq_iff (x : RelativeWeilGroup c F E) (g g' : RelativeWeilGroup c K E) :
    (∀ y : E, upperEmbedding c K z w u x g y = upperEmbedding c K z w u x g' y) ↔
      g⁻¹ * g' ∈ ideleClassSubgroup c K E := by
  rw [ideleClassSubgroup, RelativeWeilGroup.exact, MonoidHom.mem_ker, map_mul, map_inv,
    inv_mul_eq_one]
  constructor
  · intro hgg
    ext y
    have h1 := hgg y
    rw [upperEmbedding_apply, upperEmbedding_apply] at h1
    exact (projection c F E x)⁻¹.injective
      ((closurePlaceEmbedding z w).injective ((closureLift K z u).injective h1))
  · intro hgg y
    rw [upperEmbedding_apply, upperEmbedding_apply, hgg]

omit [IsScalarTower F K E] in
/-- Every place embedding of `E` at a place above `u` is an upper embedding. -/
theorem exists_upperEmbedding_eq (x : RelativeWeilGroup c F E)
    (hx : ∀ k : K, cosetEmbedding c K z w x k = placeEmbedding z u k)
    (v : FinitePlacesAbove E u.1) :
    ∃ t : RelativeWeilGroup c K E, ∀ y : E,
      upperEmbedding c K z w u x t y = placeEmbedding (F := K) u.1 v y := by
  let β := upperEmbedding c K z w u x 1
  have hβ : ∀ k : K, β (algebraMap K E k) =
      algebraMap K (AlgebraicClosure (u.1.adicCompletion K)) k := fun k =>
    (upperEmbedding_algebraMap c K z w u x hx 1 k).trans
      (IsScalarTower.algebraMap_apply K (u.1.adicCompletion K) _ k).symm
  have hpe : ∀ k : K, placeEmbedding (F := K) u.1 v (algebraMap K E k) =
      algebraMap K (AlgebraicClosure (u.1.adicCompletion K)) k := by
    intro k
    change completionClosureEmbedding u.1 v.1
      (algebraMap E (v.1.adicCompletion E) (algebraMap K E k)) = _
    rw [← FiniteExtension.completionMap_coe u.1 v.1]
    exact (completionClosureEmbedding_algebraMap u.1 v.1 _).trans
      (IsScalarTower.algebraMap_apply K (u.1.adicCompletion K) _ k).symm
  let peA : E →ₐ[K] AlgebraicClosure (u.1.adicCompletion K) :=
    { placeEmbedding (F := K) u.1 v with commutes' := hpe }
  let _ : Algebra E (AlgebraicClosure (u.1.adicCompletion K)) := β.toAlgebra
  have : IsScalarTower K E (AlgebraicClosure (u.1.adicCompletion K)) :=
    IsScalarTower.of_algebraMap_eq fun k => (hβ k).symm
  have : Normal K E := IsGalois.to_normal
  obtain ⟨t, ht⟩ := projection_surjective c K E (peA.restrictNormal' E)
  refine ⟨t, fun y => ?_⟩
  have hβt : upperEmbedding c K z w u x t y = β (projection c K E t y) := by
    rw [upperEmbedding_apply, upperEmbedding_apply, map_one, AlgEquiv.one_apply]
  rw [hβt, ht]
  change algebraMap E (AlgebraicClosure (u.1.adicCompletion K)) (peA.restrictNormal E y) = _
  rw [AlgHom.restrictNormal_commutes]
  rfl

/-- A representative in `W_{E/K}` for the place `v` of `E` above `u`: its upper embedding is the
place embedding at `v`. -/
def upperRepresentative (v : FinitePlacesAbove E u.1) : RelativeWeilGroup c K E :=
  (exists_upperEmbedding_eq c K z w u (placeRepresentative c K z w u)
    (cosetEmbedding_placeRepresentative c K z w u) v).choose

theorem upperEmbedding_upperRepresentative (v : FinitePlacesAbove E u.1) (y : E) :
    upperEmbedding c K z w u (placeRepresentative c K z w u)
        (upperRepresentative c K z w u v) y = placeEmbedding (F := K) u.1 v y :=
  (exists_upperEmbedding_eq c K z w u (placeRepresentative c K z w u)
    (cosetEmbedding_placeRepresentative c K z w u) v).choose_spec y

/-- The automorphism `y ↦ (projection t_v)⁻¹ (projection x_u y)` of `E` over `F`, which carries
the place `v` back to `w`. -/
def upperRho (v : FinitePlacesAbove E u.1) : E ≃ₐ[F] E :=
  (projection c F E (placeRepresentative c K z w u)).trans
    ((projection c K E (upperRepresentative c K z w u v)⁻¹).restrictScalars F)

theorem upperRho_apply (v : FinitePlacesAbove E u.1) (y : E) :
    upperRho c K z w u v y = projection c K E (upperRepresentative c K z w u v)⁻¹
      (projection c F E (placeRepresentative c K z w u) y) :=
  rfl

/-- The place `v` of `E` above `u` pulls back to `w` along `upperRho v`. -/
theorem finitePlaceEquiv_upperRho (v : FinitePlacesAbove E u.1) :
    finitePlaceEquiv (upperRho c K z w u v).toRingEquiv v.1 = w := by
  have hvz : v.1.asIdeal.LiesOver z.asIdeal :=
    Ideal.LiesOver.trans v.1.asIdeal u.1.asIdeal z.asIdeal
  have hqz := Langlands.ClassField.Global.liesOver_finitePlaceEquiv z v.1 (upperRho c K z w u v)
  let q := finitePlaceEquiv (upperRho c K z w u v).toRingEquiv v.1
  let φ := finiteCompletionEquiv (upperRho c K z w u v).toRingEquiv v.1
  have hφz : ∀ a : z.adicCompletion F,
      φ (FiniteExtension.completionMap z q a) = FiniteExtension.completionMap z v.1 a := by
    have h1 : Continuous (fun a => φ (FiniteExtension.completionMap z q a)) :=
      (continuous_finiteCompletionEquiv _ _).comp (FiniteExtension.continuous_completionMap z q)
    have heq := (z.denseRange_algebraMap F).equalizer h1
      (FiniteExtension.continuous_completionMap z v.1) (funext fun a => by
        simp only [Function.comp_apply, FiniteExtension.completionMap_coe]
        rw [finiteCompletionEquiv_coe]
        congr 1
        exact (upperRho c K z w u v).commutes a)
    exact fun a => congrFun heq a
  let lamE := Weil.Local.extensionClosureEquiv (padicField z) (towerPadicField z u.1)
    (completionPadicAlgHom z u.1)
  let κ : q.adicCompletion E →+* AlgebraicClosure (z.adicCompletion F) :=
    lamE.symm.toRingHom.comp ((completionClosureEmbedding u.1 v.1).comp φ.toRingHom)
  have hκ : ∀ a : z.adicCompletion F, κ (algebraMap (z.adicCompletion F) (q.adicCompletion E) a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F)) a := by
    intro a
    change lamE.symm (completionClosureEmbedding u.1 v.1 (φ (FiniteExtension.completionMap z q a))) = _
    rw [hφz, ← ClassField.Global.CompletionTower.completionMap_comp z u.1 v.1, RingHom.comp_apply,
      show completionClosureEmbedding u.1 v.1 (FiniteExtension.completionMap u.1 v.1
          (FiniteExtension.completionMap z u.1 a)) =
        algebraMap (u.1.adicCompletion K) (AlgebraicClosure (u.1.adicCompletion K))
          (FiniteExtension.completionMap z u.1 a) from
        completionClosureEmbedding_algebraMap u.1 v.1 _, RingEquiv.symm_apply_eq]
    exact (Weil.Local.extensionClosureLift_algebraMap (padicField z) (towerPadicField z u.1)
      (completionPadicAlgHom z u.1) a).symm
  obtain ⟨τ, hτ⟩ := exists_eq_comp_completionClosureEmbedding (K := E) z ⟨q, hqz⟩ κ hκ
  have key := eq_of_placeEmbedding_eq (K := E) z ⟨q, hqz⟩ ⟨w, ‹_›⟩ τ (fun y => by
    change AlgEquiv.toAlgHom τ (completionClosureEmbedding z q (algebraMap E (q.adicCompletion E) y)) =
      closurePlaceEmbedding z w y
    rw [← hτ]
    change lamE.symm (completionClosureEmbedding u.1 v.1
      (φ (algebraMap E (q.adicCompletion E) y))) = _
    rw [finiteCompletionEquiv_coe, RingEquiv.symm_apply_eq]
    change placeEmbedding (F := K) u.1 v (upperRho c K z w u v y) = _
    rw [← upperEmbedding_upperRepresentative c K z w u v, upperEmbedding_apply, upperRho_apply,
      ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply,
      aut_inv_apply_apply]
    rfl)
  exact congrArg Subtype.val key

variable (h : FundamentalClass.Restriction c)
  (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
  (hι : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (y : E),
    closurePlaceEmbedding z w (projection c F E (ι g) y) =
      AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
        (closurePlaceEmbedding z w y))

/-- On `E`, the image of `localPlaceMap u n` in `Gal(E/K)` is the conjugate by the
representative of `u` of the image of `ι`. -/
theorem projection_localPlaceMap_apply
    (n : Weil.Local.localWeilGroup (towerPadicField z u.1)) (y : E) :
    projection c K E (localPlaceMap c K z w h ι hι u n) y =
      projection c F E (placeRepresentative c K z w u)
        (projection c F E (ι (completionWeilMap z u.1 n))
          ((projection c F E (placeRepresentative c K z w u))⁻¹ y)) := by
  have h1 := projection_restrictionInclusion c F E K h (localPlaceMap c K z w h ι hι u n)
  rw [restrictionInclusion_localPlaceMap] at h1
  have h2 := congrArg (fun σ : E ≃ₐ[F] E => σ y) h1
  simp only [map_mul, map_inv, AlgEquiv.mul_apply] at h2
  exact h2.symm

/-- Left multiplication by `localPlaceMap u ℓ` composes the upper embedding with the Galois
image of `ℓ` in `G_{K_u}`. -/
theorem upperEmbedding_localPlaceMap_mul
    (ℓ : Weil.Local.localWeilGroup (towerPadicField z u.1)) (g : RelativeWeilGroup c K E)
    (y : E) :
    upperEmbedding c K z w u (placeRepresentative c K z w u)
        (localPlaceMap c K z w h ι hι u ℓ * g) y =
      AlgEquiv.toAlgHom (localGaloisImage K z u ℓ)
        (upperEmbedding c K z w u (placeRepresentative c K z w u) g y) := by
  rw [upperEmbedding_apply, upperEmbedding_apply, map_mul, AlgEquiv.mul_apply,
    projection_localPlaceMap_apply, aut_inv_apply_apply, hι]
  exact Weil.Local.extensionClosureLift_galoisMap _ _ _ _ _

/-- The subgroup of `W_{K_u}` mapping into the image of `W_{E_w}` in `W_{F_z}`. -/
abbrev upperSubgroup : Subgroup (Weil.Local.localWeilGroup (towerPadicField z u.1)) :=
  (completionWeilMap z w).toMonoidHom.range.comap (completionWeilMap z u.1).toMonoidHom

include hι in
theorem mem_upperSubgroup_iff (l : Weil.Local.localWeilGroup (towerPadicField z u.1)) :
    l ∈ upperSubgroup K z w u ↔ localPlaceMap c K z w h ι hι u l ∈ ideleClassSubgroup c K E := by
  rw [ideleClassSubgroup, RelativeWeilGroup.exact, MonoidHom.mem_ker, AlgEquiv.ext_iff,
    upperSubgroup, Subgroup.mem_comap, completionWeilMap, Weil.Local.extensionWeilMap_range,
    Subgroup.mem_comap]
  rw [← placeEmbedding_fixed_iff z ⟨w, ‹_›⟩]
  simp only [projection_localPlaceMap_apply, AlgEquiv.one_apply]
  constructor
  · intro hfix y
    have h1 := hfix ((projection c F E (placeRepresentative c K z w u))⁻¹ y)
    change AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z)
      (completionWeilMap z u.1 l)) (closurePlaceEmbedding z w _) =
        closurePlaceEmbedding z w _ at h1
    rw [← hι] at h1
    rw [(closurePlaceEmbedding z w).injective h1, aut_apply_inv_apply]
  · intro hfix y
    have h1 := hfix (projection c F E (placeRepresentative c K z w u) y)
    rw [aut_inv_apply_apply] at h1
    have hy := (projection c F E (placeRepresentative c K z w u)).injective h1
    change AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z)
      (completionWeilMap z u.1 l)) (closurePlaceEmbedding z w y) = closurePlaceEmbedding z w y
    rw [← hι, hy]

include hι in
/-- The double cosets `ψ(W_{K_u}) t_v C_E` cover `W_{E/K}`. -/
theorem exists_eq_localPlaceMap_mul (g : RelativeWeilGroup c K E) :
    ∃ (v : FinitePlacesAbove E u.1) (l : Weil.Local.localWeilGroup (towerPadicField z u.1)),
      ∃ m ∈ ideleClassSubgroup c K E,
        g = localPlaceMap c K z w h ι hι u l * upperRepresentative c K z w u v * m := by
  obtain ⟨v, τ, hτ⟩ := exists_placeEmbedding (F := K) (K := E) u.1
    (upperEmbedding c K z w u (placeRepresentative c K z w u) g)
    (upperEmbedding_algebraMap c K z w u _ (cosetEmbedding_placeRepresentative c K z w u) g)
  obtain ⟨ℓ, hℓ⟩ := exists_dense_placeEmbedding (F := K) (K := E) u.1
    (localGaloisImage K z u) (localGaloisImage_denseRange K z u) v τ
  have key : ∀ y : E, upperEmbedding c K z w u (placeRepresentative c K z w u)
      (localPlaceMap c K z w h ι hι u ℓ * upperRepresentative c K z w u v) y =
        upperEmbedding c K z w u (placeRepresentative c K z w u) g y := by
    intro y
    rw [hτ y, upperEmbedding_localPlaceMap_mul, upperEmbedding_upperRepresentative]
    exact hℓ y
  exact ⟨v, ℓ, _, (upperEmbedding_eq_iff c K z w u _ _ _).mp key,
    (mul_inv_cancel_left _ _).symm⟩

include hι in
/-- The double cosets of distinct places of `E` above `u` are distinct. -/
theorem upperRepresentative_injective (i j : FinitePlacesAbove E u.1)
    (l : Weil.Local.localWeilGroup (towerPadicField z u.1)) (m : RelativeWeilGroup c K E)
    (hm : m ∈ ideleClassSubgroup c K E)
    (hij : upperRepresentative c K z w u j =
      localPlaceMap c K z w h ι hι u l * upperRepresentative c K z w u i * m) :
    i = j := by
  have hmem : (localPlaceMap c K z w h ι hι u l * upperRepresentative c K z w u i * m)⁻¹ *
      (localPlaceMap c K z w h ι hι u l * upperRepresentative c K z w u i) ∈
        ideleClassSubgroup c K E := by
    have he : (localPlaceMap c K z w h ι hι u l * upperRepresentative c K z w u i * m)⁻¹ *
        (localPlaceMap c K z w h ι hι u l * upperRepresentative c K z w u i) = m⁻¹ := by
      group
    rw [he]
    exact Subgroup.inv_mem _ hm
  apply eq_of_placeEmbedding_eq (F := K) (K := E) u.1 i j (localGaloisImage K z u l)
  intro y
  rw [← upperEmbedding_upperRepresentative c K z w u i,
    ← upperEmbedding_localPlaceMap_mul c K z w u h ι hι,
    ← upperEmbedding_upperRepresentative c K z w u j, hij]
  exact ((upperEmbedding_eq_iff c K z w u _ _ _).mpr hmem y).symm

omit [IsGalois F E] in
theorem mem_iff_inv_mul_mul_mem {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]
    (a g : G) : a ∈ H ↔ g⁻¹ * a * g ∈ H :=
  ⟨fun ha => by simpa using hH.conj_mem a ha g⁻¹,
    fun ha => by simpa [mul_assoc] using hH.conj_mem _ ha g⟩

/-- On the subgroup `upperSubgroup`, the reciprocity map of `E_w` read through
`W_{K_u} → W_{F_z} ⊇ W_{E_w}`. -/
def upperReciprocity (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w)) :
    upperSubgroup K z w u →* (w.adicCompletion E)ˣ :=
  letI := (towerPadicField z w).canonicalTopologicalData.topology
  (LocalFactor.RankOne.reciprocityUnits (towerPadicField z w) e).toMonoidHom.comp
    ((InductionAlong.rangeInverse (completionWeilMap z w).toMonoidHom
        (Weil.Local.extensionWeilMap_injective _ _ _)).comp
      ((completionWeilMap z u.1).toMonoidHom.subgroupComap _))

variable (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
  (hι3 : ∀ y : Weil.Local.localWeilGroup (towerPadicField z w),
    ι (completionWeilMap z w y) =
      (inclusion c F E (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
        (LocalFactor.RankOne.reciprocityUnits (towerPadicField z w) e y)))⁻¹)

include hι3 in
/-- On `upperSubgroup`, `localPlaceMap u` is the inverse of the inclusion of the conjugate
idele class of `upperReciprocity`. -/
theorem localPlaceMap_upperSubgroup (k : upperSubgroup K z w u) :
    localPlaceMap c K z w h ι hι u k =
      (inclusion c K E (ideleClassEquiv
        (projection c F E (placeRepresentative c K z w u)).toRingEquiv
        (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w (upperReciprocity K z w u e k))))⁻¹ := by
  apply restrictionInclusion_injective c F E K h
  rw [restrictionInclusion_localPlaceMap, map_inv, restrictionInclusion_inclusion]
  have hm : completionWeilMap z u.1 (k : Weil.Local.localWeilGroup (towerPadicField z u.1)) =
      completionWeilMap z w (InductionAlong.rangeInverse (completionWeilMap z w).toMonoidHom
        (Weil.Local.extensionWeilMap_injective _ _ _)
        ((completionWeilMap z u.1).toMonoidHom.subgroupComap _ k)) :=
    (InductionAlong.apply_rangeInverse (completionWeilMap z w).toMonoidHom
      (Weil.Local.extensionWeilMap_injective _ _ _)
      ((completionWeilMap z u.1).toMonoidHom.subgroupComap _ k)).symm
  rw [hm, hι3, ← conjugation]
  group
  rfl

include hι3 in
theorem conj_localPlaceMap_upperSubgroup (t : RelativeWeilGroup c K E)
    (k : upperSubgroup K z w u) :
    t⁻¹ * localPlaceMap c K z w h ι hι u k * t =
      (inclusion c K E (ideleClassEquiv (projection c K E t⁻¹).toRingEquiv
        (ideleClassEquiv (projection c F E (placeRepresentative c K z w u)).toRingEquiv
          (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w (upperReciprocity K z w u e k)))))⁻¹ := by
  rw [localPlaceMap_upperSubgroup c K z w u h ι hι e hι3, ← conjugation c K E t⁻¹, inv_inv]
  group

/-- The contribution of the representative `t`: `a ↦ (t⁻¹ x_u · [a]_w)⁻¹` in `C_E`. -/
def upperTerm (t : RelativeWeilGroup c K E) :
    (w.adicCompletion E)ˣ →* IdeleClassGroup (𝓞 E) E :=
  (@invMonoidHom (IdeleClassGroup (𝓞 E) E) _).comp ((((ideleClassEquiv (projection c K E t⁻¹).toRingEquiv).toMulEquiv.toMonoidHom).comp
    (ideleClassEquiv (projection c F E (placeRepresentative c K z w u)).toRingEquiv).toMulEquiv.toMonoidHom).comp
      (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w))

theorem upperTerm_apply (t : RelativeWeilGroup c K E) (a : (w.adicCompletion E)ˣ) :
    upperTerm c K z w u t a =
      (ideleClassEquiv (projection c K E t⁻¹).toRingEquiv
        (ideleClassEquiv (projection c F E (placeRepresentative c K z w u)).toRingEquiv
          (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w a)))⁻¹ :=
  rfl

include hι3 in
/-- The transfer `W_{E/K} → C_E` on the image of `localPlaceMap u`, as a product over the
places of `E` above `u` of conjugates of the transfer of `upperReciprocity`. -/
theorem ideleTransfer_localPlaceMap (y : Weil.Local.localWeilGroup (towerPadicField z u.1)) :
    ideleTransfer c K E (localPlaceMap c K z w h ι hι u y) =
      ∏ v : FinitePlacesAbove E u.1, upperTerm c K z w u (upperRepresentative c K z w u v)
        (MonoidHom.transfer (upperReciprocity K z w u e) y) := by
  rw [ideleTransfer_apply]
  refine (Langlands.GroupTheory.Transfer.transfer_comp_eq_prod_of_conj
    (ψ := (localPlaceMap c K z w h ι hι u).toMonoidHom) (t := upperRepresentative c K z w u)
    (K := fun _ => upperSubgroup K z w u)
    (hK := fun v l => (mem_upperSubgroup_iff c K z w u h ι hι l).trans
      (mem_iff_inv_mul_mul_mem _ _))
    _ (fun v => (upperTerm c K z w u (upperRepresentative c K z w u v)).comp
      (upperReciprocity K z w u e)) ?_ (exists_eq_localPlaceMap_mul c K z w u h ι hι)
    (upperRepresentative_injective c K z w u h ι hι) y).trans ?_
  rotate_left
  · refine Finset.prod_congr rfl fun v _ => ?_
    exact Langlands.GroupTheory.Transfer.transfer_comp _ _ _
  · intro v k
    have hk := conj_localPlaceMap_upperSubgroup c K z w u h ι hι e hι3
      (upperRepresentative c K z w u v) k
    have key : ∀ (X : IdeleClassGroup (𝓞 E) E) (q : ideleClassSubgroup c K E),
        (q : RelativeWeilGroup c K E) = (inclusion c K E X)⁻¹ →
          (ideleClassSubgroupEquiv c K E).toMulEquiv.toMonoidHom q = X⁻¹ := by
      intro X q hq
      have hq' : q = ⟨inclusion c K E X⁻¹, X⁻¹, rfl⟩ := Subtype.ext (hq.trans (map_inv _ _).symm)
      rw [hq']
      exact ideleClassSubgroupEquiv_inclusion c K E X⁻¹
    rw [MonoidHom.comp_apply, upperTerm_apply]
    refine Eq.symm (key _ _ ?_)
    exact hk

/-- Each term of `ideleTransfer_localPlaceMap`, evaluated on a unit of `K_u` sent to `E_w` by
`twistedMap`, is the inverse of the image of that unit at the place `v`. -/
theorem upperTerm_twistedMap (v : FinitePlacesAbove E u.1) (a : (u.1.adicCompletion K)ˣ) :
    upperTerm c K z w u (upperRepresentative c K z w u v)
        (Units.map (twistedMap c K z w u).toRingHom.toMonoidHom a) =
      (IdeleClassGroup.ofAdicCompletion (𝓞 E) E v.1
        (Units.map (FiniteExtension.completionMap u.1 v.1).toMonoidHom a))⁻¹ := by
  rw [upperTerm_apply]
  congr 1
  have htrans : ∀ X : IdeleClassGroup (𝓞 E) E,
      ideleClassEquiv (projection c K E (upperRepresentative c K z w u v)⁻¹).toRingEquiv
        (ideleClassEquiv (projection c F E (placeRepresentative c K z w u)).toRingEquiv X) =
      ideleClassEquiv (upperRho c K z w u v).toRingEquiv X := by
    intro X
    rw [show (upperRho c K z w u v).toRingEquiv =
      (projection c F E (placeRepresentative c K z w u)).toRingEquiv.trans
        (projection c K E (upperRepresentative c K z w u v)⁻¹).toRingEquiv from rfl,
      ideleClassEquiv_trans]
    rfl
  rw [htrans]
  refine ideleClassEquiv_ofAdicCompletion_units_map (K := K) (z := z) (u := u)
    (upperRho c K z w u v) v w (finitePlaceEquiv_upperRho c K z w u v)
    (twistedMap c K z w u) (fun k => ?_) a
  rw [twistedMap_algebraMap]
  congr 1
  change (projection c F E (placeRepresentative c K z w u))⁻¹ (algebraMap K E k) =
    (projection c F E (placeRepresentative c K z w u)).symm
      ((projection c K E (upperRepresentative c K z w u v)⁻¹).symm (algebraMap K E k))
  rw [AlgEquiv.commutes]
  rfl

include hι3 in
/-- Condition 1 for `localPlaceMap u`, given the transfer of `upperReciprocity` (the local
transfer square for `K_u ⊆ E_w` along `twistedMap`) and the idele identity for the places
of `E` above `u`. -/
theorem transfer_localPlaceMap_of_local (y : Weil.Local.localWeilGroup (towerPadicField z u.1))
    (a : (u.1.adicCompletion K)ˣ)
    (htower : MonoidHom.transfer (upperReciprocity K z w u e) y =
      Units.map (twistedMap c K z w u).toRingHom.toMonoidHom a)
    (hG : ∏ v : FinitePlacesAbove E u.1, IdeleClassGroup.ofAdicCompletion (𝓞 E) E v.1
        (Units.map (FiniteExtension.completionMap u.1 v.1).toMonoidHom a) =
      ideleClassInclusion (K := K) (L := E) (IdeleClassGroup.ofAdicCompletion (𝓞 K) K u.1 a)) :
    transfer c K E (localPlaceMap c K z w h ι hι u y) =
      (IdeleClassGroup.ofAdicCompletion (𝓞 K) K u.1 a)⁻¹ := by
  symm
  apply eq_transfer_of_ideleClassInclusion_eq c K E
  rw [map_inv, ← hG, ideleTransfer_localPlaceMap c K z w u h ι hι e hι3 y, htower,
    ← Finset.prod_inv_distrib (f := fun v : FinitePlacesAbove E u.1 =>
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E v.1
        (Units.map (FiniteExtension.completionMap u.1 v.1).toMonoidHom a))]
  exact Finset.prod_congr rfl fun v _ => (upperTerm_twistedMap c K z w u v a).symm

end Upper

end Langlands.ClassField.Global.RelativeWeilGroup
