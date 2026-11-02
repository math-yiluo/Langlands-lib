import Langlands.Global.Arithmetic.CMPairedPlaceAssembly
import Langlands.Global.Arithmetic.CMGaloisModel
import Langlands.Global.Arithmetic.QuadraticPadicSplittingProof

/-!
# CM paired-place realization from a CM rational Galois model

Let `Ω / ℚ_[p]` be a finite Galois extension containing `F̃`, generated over `ℚ_[p]` by a CM
Galois number field `N ⊆ Ω`. Suppose `N` contains a square root `x_a` of a negative rational
`a` that is a square in `ℚ_[p]`, a square root `x_d` of a positive rational `d`, both sent into
`ℚ_[p]`, and a central automorphism `s` of `N` fixing `x_a` and negating `x_d`. The model fields
`E ⊆ E' ⊆ L` of `N` cut out by `F ⊆ F' ⊆ F̃` are then CM fields with all the data of Harris's
paired-place setup, with `K₀ = ℚ(x_a)`.
-/

noncomputable section

universe uF

namespace Langlands.Global.CMRealization

open NumberField IntermediateField FieldRealization
open Harris LocalFactor.CommonClosure GeneralPosition AdelicFunctoriality

/-- An automorphism of a number field `N` preserving the image of a number field `S` restricts
to an automorphism of `S`. -/
theorem exists_restrict {N : Type*} [Field N] [NumberField N] {S : Type*} [Field S]
    [NumberField S] [Algebra S N] (u : N ≃ₐ[ℚ] N)
    (hS : ∀ y, ∃ z, algebraMap S N z = u (algebraMap S N y)) :
    ∃ f : S ≃+* S, ∀ y, algebraMap S N (f y) = u (algebraMap S N y) := by
  choose g hg using hS
  have inj := (algebraMap S N).injective
  let g₀ : S →ₐ[ℚ] S :=
    { toFun := g
      map_one' := inj (by simp [hg])
      map_mul' := fun x y => inj (by simp [hg])
      map_zero' := inj (by simp [hg])
      map_add' := fun x y => inj (by simp [hg])
      commutes' := fun r => inj (by
        rw [hg, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]) }
  exact ⟨(AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)).toRingEquiv, hg⟩

/-- Generation over a smaller ring implies generation over a larger one. -/
theorem adjoin_eq_top_of_restrictScalars {R K A : Type*} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] [Algebra K A] [IsScalarTower R K A] {s : Set A}
    (h : Algebra.adjoin R s = ⊤) : Algebra.adjoin K s = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin R s := h ▸ Algebra.mem_top
  have hle : Algebra.adjoin R s ≤ (Algebra.adjoin K s).restrictScalars R :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := K))
  exact hle hx

/-- A negative rational number has no rational square root. -/
theorem not_isSquare_of_neg {a : ℚ} (ha : a < 0) : ¬ IsSquare a := by
  rintro ⟨r, rfl⟩
  nlinarith [mul_self_nonneg r]

/-- The CM and quadratic parts of the target: for a tower of number fields stable under complex
conjugation of a CM field `M`, and a square root `x ∈ E` of a negative rational which is a
square in `ℚ_[p]`, the three fields are CM and `ℚ(x)` is split imaginary quadratic and
generates each of them over its maximal real subfield. -/
theorem cmQuadratic (p : ℕ) [Fact p.Prime] {E E' L : Type} [Field E] [Field E'] [Field L]
    [NumberField E] [NumberField E'] [NumberField L] [Algebra E E'] [Algebra E L]
    {M : Type*} [Field M] [NumberField M] [IsCMField M] [Algebra E M] [Algebra E' M]
    [Algebra L M]
    (hE : ∀ y : E, ∃ z : E, algebraMap E M z = conjQ M (algebraMap E M y))
    (hE' : ∀ y : E', ∃ z : E', algebraMap E' M z = conjQ M (algebraMap E' M y))
    (hL : ∀ y : L, ∃ z : L, algebraMap L M z = conjQ M (algebraMap L M y))
    {a : ℚ} (ha : a < 0) (haq : IsSquare (algebraMap ℚ ℚ_[p] a)) {x : E}
    (hx : x ^ 2 = algebraMap ℚ E a) :
    IsCMField E ∧ IsCMField E' ∧ IsCMField L ∧ IsSplitImaginaryQuadratic p ℚ⟮x⟯ ∧
      maximalRealSubfield E ⊔ ℚ⟮x⟯.toSubfield = ⊤ ∧
      maximalRealSubfield E' ⊔ ℚ⟮x⟯.toSubfield.map (algebraMap E E') = ⊤ ∧
      maximalRealSubfield L ⊔ ℚ⟮x⟯.toSubfield.map (algebraMap E L) = ⊤ := by
  have hx' : (algebraMap E E' x) ^ 2 = algebraMap ℚ E' a := by
    rw [← map_pow, hx, ← IsScalarTower.algebraMap_apply]
  have hxL : (algebraMap E L x) ^ 2 = algebraMap ℚ L a := by
    rw [← map_pow, hx, ← IsScalarTower.algebraMap_apply]
  have hna := not_isSquare_of_neg ha
  have hfin : Module.finrank ℚ ℚ⟮x⟯ = 2 := squareRoot_finrank hna hx
  obtain ⟨v₁, v₂, -, -, hne, hp₁, hp₂, -⟩ :=
    quadraticPadicSplitting.{0} p inferInstance ℚ⟮x⟯ inferInstance inferInstance hfin
      (rationalRootField_two_embeddings hna hx haq)
  refine ⟨isCMField_of_sq_neg hE ha hx, isCMField_of_sq_neg hE' ha hx',
    isCMField_of_sq_neg hL ha hxL,
    ⟨hfin, rationalRootField_totallyComplex ha hx, v₁, v₂, hne, hp₁, hp₂⟩,
    maximalRealSubfield_sup_eq_top hE ha hx _ (mem_adjoin_simple_self ℚ x),
    maximalRealSubfield_sup_eq_top hE' ha hx' _
      (Subfield.mem_map.mpr ⟨x, mem_adjoin_simple_self ℚ x, rfl⟩),
    maximalRealSubfield_sup_eq_top hL ha hxL _
      (Subfield.mem_map.mpr ⟨x, mem_adjoin_simple_self ℚ x, rfl⟩)⟩

section Model

variable (p : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω] [CharZero Ω]
  (N : Type) [Field N] [NumberField N] [IsGalois ℚ N] [Algebra N Ω]

omit [IsGalois ℚ N] in
/-- An element of `N` sent into `ℚ_[p]` lies in every model field. -/
theorem mem_modelField_of_padic (A : Type*) [Field A] [Algebra ℚ_[p] A] [Algebra A Ω]
    [IsScalarTower ℚ_[p] A Ω] {y : N} (hy : ∃ r : ℚ_[p], algebraMap N Ω y = algebraMap ℚ_[p] Ω r) :
    y ∈ modelField p Ω N A := by
  obtain ⟨r, hr⟩ := hy
  exact (mem_modelField p Ω N A).mpr ⟨algebraMap ℚ_[p] A r, by
    rw [← IsScalarTower.algebraMap_apply, hr]⟩

/-- A model field is stable under every central automorphism of `N`. -/
theorem modelField_central (A : Type*) [Field A] [Algebra ℚ_[p] A] [Algebra A Ω]
    [IsScalarTower ℚ_[p] A Ω] (u : N ≃ₐ[ℚ] N)
    (hu : ∀ (σ : N ≃ₐ[ℚ] N) (x : N), σ (u x) = u (σ x)) (y : modelField p Ω N A) :
    ∃ z : modelField p Ω N A,
      algebraMap (modelField p Ω N A) N z = u (algebraMap (modelField p Ω N A) N y) :=
  ⟨⟨u y, mem_of_central _ hu y.2⟩, rfl⟩

/-- A top model field is stable under every central automorphism of `N`. -/
theorem topModel_central (A B : Type*) [Field A] [Field B] [Algebra ℚ_[p] A]
    [Algebra ℚ_[p] B] [Algebra A B] [IsScalarTower ℚ_[p] A B] [Algebra A Ω] [Algebra B Ω]
    [IsScalarTower A B Ω] [IsScalarTower ℚ_[p] A Ω] [IsScalarTower ℚ_[p] B Ω] (u : N ≃ₐ[ℚ] N)
    (hu : ∀ (σ : N ≃ₐ[ℚ] N) (x : N), σ (u x) = u (σ x)) (y : topModel p Ω N A B) :
    ∃ z : topModel p Ω N A B,
      algebraMap (topModel p Ω N A B) N z = u (algebraMap (topModel p Ω N A B) N y) :=
  ⟨⟨u y, mem_of_central (modelField p Ω N B) hu y.2⟩, rfl⟩

end Model

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)

set_option maxHeartbeats 400000 in
/-- Harris's paired-place realization, from a CM rational Galois model `N` of a finite Galois
extension `Ω / ℚ_[p]` containing `F̃`, with square roots `x_a` of `a < 0` and `x_d` of `d > 0`
sent into `ℚ_[p]` and a central automorphism `s` of `N` fixing `x_a` and negating `x_d`. -/
theorem pairedPlaceRealization_of_model (Ω : Type*) [Field Ω] [CharZero Ω] [Algebra ℚ_[p] Ω]
    [FiniteDimensional ℚ_[p] Ω] [IsGalois ℚ_[p] Ω] [a₁ : Algebra ℚ_[p] F'.field]
    [a₂ : Algebra ℚ_[p] (galoisClosure F F').field] [t₁ : IsScalarTower ℚ_[p] F.Carrier F'.field]
    [t₂ : IsScalarTower ℚ_[p] F.Carrier (galoisClosure F F').field]
    [aΩ : Algebra (galoisClosure F F').field Ω]
    [tΩ : IsScalarTower ℚ_[p] (galoisClosure F F').field Ω]
    (N : Type) [Field N] [NumberField N] [IsGalois ℚ N] [IsCMField N] [Algebra N Ω]
    (hι : IntermediateField.adjoin ℚ_[p] (Set.range (algebraMap N Ω)) = ⊤)
    {a d : ℚ} (ha : a < 0) (hd : 0 < d) (haq : IsSquare (algebraMap ℚ ℚ_[p] a))
    {xa xd : N} (hxa : xa ^ 2 = algebraMap ℚ N a) (hxd : xd ^ 2 = algebraMap ℚ N d)
    (hra : ∃ r : ℚ_[p], algebraMap N Ω xa = algebraMap ℚ_[p] Ω r)
    (hrd : ∃ r : ℚ_[p], algebraMap N Ω xd = algebraMap ℚ_[p] Ω r)
    (s : N ≃ₐ[ℚ] N) (hs : ∀ (σ : N ≃ₐ[ℚ] N) (x : N), σ (s x) = s (σ x))
    (hsa : s xa = xa) (hsd : s xd = -xd) :
    letI := F.canonicalTopology
    letI := (fieldData F F').topology
    letI := (fieldData F (galoisClosure F F')).topology
    ∃ (E E' L : Type) (_ : Field E) (_ : Field E') (_ : Field L)
      (_ : NumberField E) (_ : NumberField E') (_ : NumberField L)
      (_ : IsCMField E) (_ : IsCMField E') (_ : IsCMField L)
      (_ : Algebra E E') (_ : Algebra E L) (_ : Algebra E' L)
      (_ : IsScalarTower E E' L) (_ : IsNormalClosure E E' L)
      (K₀ : IntermediateField ℚ E)
      (P Ps : PlaceDatum F F' E E' L)
      (φ : FiniteCompletion E' P.v' ≃+* F'.field)
      (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
      (θ : (L ≃ₐ[E] L) ≃*
        ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
      IsSplitImaginaryQuadratic p K₀ ∧
      maximalRealSubfield E ⊔ K₀.toSubfield = ⊤ ∧
      maximalRealSubfield E' ⊔ K₀.toSubfield.map (algebraMap E E') = ⊤ ∧
      maximalRealSubfield L ⊔ K₀.toSubfield.map (algebraMap E L) = ⊤ ∧
      Module.finrank E E' = Module.finrank F.Carrier F'.field ∧
      Module.finrank E L = Module.finrank F.Carrier (galoisClosure F F').field ∧
      List.Pairwise (· ≠ ·) [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v] ∧
      (∀ v ∈ [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v],
        (p : 𝓞 E) ∈ v.asIdeal ∧ HasUniquePlaceAbove L v) ∧
      (∀ Q ∈ [P, Ps],
        Q.IsCompatible ∧
        Continuous Q.iso ∧ Continuous Q.iso.symm ∧
        Continuous Q.isoTilde ∧ Continuous Q.isoTilde.symm ∧
        ∀ (σ : L ≃ₐ[E] L) (x : L),
          θ σ (Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) x)) =
            Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) (σ x))) ∧
      Continuous φ ∧ Continuous φ.symm ∧
      Continuous φs ∧ Continuous φs.symm ∧
      (∀ x : FiniteCompletion E P.v,
        φ (FiniteExtension.completionMap P.v P.v' x) =
          algebraMap F.Carrier F'.field (P.iso x)) ∧
      (∀ y : FiniteCompletion E' P.v',
        ((φ y : F'.field) : AlgebraicClosure F.Carrier) =
          ((P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde y) :
            (galoisClosure F F').field) : AlgebraicClosure F.Carrier)) ∧
      (∀ x : FiniteCompletion E Ps.v,
        φs (FiniteExtension.completionMap Ps.v Ps.v' x) =
          algebraMap F.Carrier F'.field (Ps.iso x)) ∧
      (∀ y : FiniteCompletion E' Ps.v',
        ((φs y : F'.field) : AlgebraicClosure F.Carrier) =
          ((Ps.isoTilde (FiniteExtension.completionMap Ps.v' Ps.vTilde y) :
            (galoisClosure F F').field) : AlgebraicClosure F.Carrier)) := by
  -- The tower `F ⊆ F' ⊆ F̃ ⊆ Ω`.
  let : Algebra F'.field (galoisClosure F F').field :=
    (IntermediateField.inclusion (le_galoisClosure F F')).toAlgebra
  let : Algebra F.Carrier Ω :=
    ((algebraMap (galoisClosure F F').field Ω).comp
      (algebraMap F.Carrier (galoisClosure F F').field)).toAlgebra
  let : Algebra F'.field Ω :=
    ((algebraMap (galoisClosure F F').field Ω).comp
      (algebraMap F'.field (galoisClosure F F').field)).toAlgebra
  have : IsScalarTower F.Carrier F'.field (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F.Carrier (galoisClosure F F').field Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F'.field (galoisClosure F F').field Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F.Carrier F'.field Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ_[p] F'.field (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier F'.field,
        IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier (galoisClosure F F').field]
      rfl
  have : IsScalarTower ℚ_[p] F.Carrier Ω :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (galoisClosure F F').field Ω,
        IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier (galoisClosure F F').field]
      rfl
  have : IsScalarTower ℚ_[p] F'.field Ω :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (galoisClosure F F').field Ω,
        IsScalarTower.algebraMap_apply ℚ_[p] F'.field (galoisClosure F F').field]
      rfl
  let : Module ℚ_[p] F'.field := Algebra.toModule
  let : Module ℚ_[p] (galoisClosure F F').field := Algebra.toModule
  have : FiniteDimensional ℚ_[p] F'.field := FiniteDimensional.trans ℚ_[p] F.Carrier F'.field
  have : FiniteDimensional ℚ_[p] (galoisClosure F F').field :=
    FiniteDimensional.trans ℚ_[p] F.Carrier (galoisClosure F F').field
  have := Algebra.charZero_of_charZero ℚ_[p] F.Carrier
  have : IsGalois F.Carrier (galoisClosure F F').field :=
    inferInstanceAs (IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier F'.field (AlgebraicClosure F.Carrier)))
  -- The model tower `E ⊆ E' ⊆ L` inside `N`.
  have hle : topModel p Ω N F.Carrier F'.field ≤
      topModel p Ω N F.Carrier (galoisClosure F F').field := fun y hy =>
    modelField_le p Ω N F'.field (galoisClosure F F').field hy
  let : Algebra (topModel p Ω N F.Carrier F'.field)
      (topModel p Ω N F.Carrier (galoisClosure F F').field) :=
    (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower (modelField p Ω N F.Carrier) (topModel p Ω N F.Carrier F'.field)
      (topModel p Ω N F.Carrier (galoisClosure F F').field) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isGalois_topModel p Ω N F.Carrier (galoisClosure F F').field hι
  -- CM structures and the imaginary quadratic field.
  have hxaE : xa ∈ modelField p Ω N F.Carrier := mem_modelField_of_padic p Ω N F.Carrier hra
  have hxdE : xd ∈ modelField p Ω N F.Carrier := mem_modelField_of_padic p Ω N F.Carrier hrd
  have hxa0 : xa ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero] at hxa
    exact ha.ne hxa
  have hxd0 : xd ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero] at hxd
    exact hd.ne' hxd
  obtain ⟨hCM, hCM', hCML, hK₀, hsup, hsup', hsupL⟩ :=
    cmQuadratic (M := N) p (E := modelField p Ω N F.Carrier)
      (E' := topModel p Ω N F.Carrier F'.field)
      (L := topModel p Ω N F.Carrier (galoisClosure F F').field)
      (modelField_central p Ω N F.Carrier (conjQ N) conjQ_central)
      (topModel_central p Ω N F.Carrier F'.field (conjQ N) conjQ_central)
      (topModel_central p Ω N F.Carrier (galoisClosure F F').field (conjQ N) conjQ_central)
      ha haq (x := ⟨xa, hxaE⟩) ((algebraMap (modelField p Ω N F.Carrier) N).injective (by
        rw [map_pow, ← IsScalarTower.algebraMap_apply]
        exact hxa))
  -- The embeddings into the local fields.
  set jE := baseEmbedding p Ω N F.Carrier with hjE
  set jE' := topEmbedding p Ω N F.Carrier F'.field with hjE'
  set jL := topEmbedding p Ω N F.Carrier (galoisClosure F F').field with hjL
  have hE := adjoin_range_baseEmbedding p Ω N F.Carrier hι
  have hE' : Algebra.adjoin F.Carrier (Set.range jE') = ⊤ :=
    adjoin_eq_top_of_restrictScalars (R := ℚ_[p])
      (adjoin_range_topEmbedding p Ω N F.Carrier F'.field hι)
  have hL : Algebra.adjoin F.Carrier (Set.range jL) = ⊤ :=
    adjoin_eq_top_of_restrictScalars (R := ℚ_[p])
      (adjoin_range_topEmbedding p Ω N F.Carrier (galoisClosure F F').field hι)
  have hcE : ∀ x : modelField p Ω N F.Carrier,
      jL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) x) =
        algebraMap F.Carrier (galoisClosure F F').field (jE x) :=
    topEmbedding_algebraMap p Ω N F.Carrier (galoisClosure F F').field
  have hcE' : ∀ y : topModel p Ω N F.Carrier F'.field,
      ((jL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) y) :
        (galoisClosure F F').field) : AlgebraicClosure F.Carrier) =
        ((jE' y : F'.field) : AlgebraicClosure F.Carrier) := by
    intro y
    have h : jL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) y) =
        algebraMap F'.field (galoisClosure F F').field (jE' y) := by
      apply (algebraMap (galoisClosure F F').field Ω).injective
      rw [hjL, algebraMap_topEmbedding]
      exact (algebraMap_topEmbedding p Ω N F.Carrier F'.field y).symm
    rw [h]
    rfl
  obtain ⟨θ, hθ⟩ := exists_galoisEquiv p Ω N F.Carrier (galoisClosure F F').field hι
  -- The twisting automorphisms, restricted from `s`.
  obtain ⟨t, ht⟩ := exists_restrict s (modelField_central p Ω N F.Carrier s hs)
  obtain ⟨t', ht'⟩ := exists_restrict s (topModel_central p Ω N F.Carrier F'.field s hs)
  obtain ⟨tL, htL⟩ :=
    exists_restrict s (topModel_central p Ω N F.Carrier (galoisClosure F F').field s hs)
  have injL := (algebraMap (topModel p Ω N F.Carrier (galoisClosure F F').field) N).injective
  have injE := (algebraMap (modelField p Ω N F.Carrier) N).injective
  have hsE : ∀ x : modelField p Ω N F.Carrier,
      tL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) x) =
        algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) (t x) :=
    fun x => injL (by rw [htL]; exact (ht x).symm)
  have hsE' : ∀ y : topModel p Ω N F.Carrier F'.field,
      tL (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) y) =
        algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) (t' y) :=
    fun y => injL (by rw [htL]; exact (ht' y).symm)
  have hsσ : ∀ (σ : topModel p Ω N F.Carrier (galoisClosure F F').field ≃ₐ[modelField p Ω N F.Carrier]
      topModel p Ω N F.Carrier (galoisClosure F F').field) (x), σ (tL x) = tL (σ x) := by
    intro σ x
    apply injL
    rw [← AlgEquiv.liftNormal_commutes σ N, htL, htL, ← AlgEquiv.liftNormal_commutes σ N]
    exact hs ((σ.liftNormal N).restrictScalars ℚ) _
  -- Complex conjugation on `L`.
  have hc : ∀ x : modelField p Ω N F.Carrier,
      (IsCMField.complexConj (topModel p Ω N F.Carrier (galoisClosure F F').field)).toRingEquiv
        (algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field) x) =
        algebraMap _ (topModel p Ω N F.Carrier (galoisClosure F F').field)
          (IsCMField.complexConj (modelField p Ω N F.Carrier) x) := by
    intro x
    apply injL
    change algebraMap _ N (IsCMField.complexConj _ _) = _
    rw [algebraMap_complexConj]
    exact (algebraMap_complexConj (M := N) x).symm
  -- The two separating elements.
  obtain ⟨ra, hra'⟩ := hra
  obtain ⟨rd, hrd'⟩ := hrd
  have hjxa : jE ⟨xa, hxaE⟩ = algebraMap ℚ_[p] F.Carrier ra := by
    apply (algebraMap F.Carrier Ω).injective
    rw [hjE, algebraMap_baseEmbedding, ← IsScalarTower.algebraMap_apply]
    exact hra'
  have hjxd : jE ⟨xd, hxdE⟩ = algebraMap ℚ_[p] F.Carrier rd := by
    apply (algebraMap F.Carrier Ω).injective
    rw [hjE, algebraMap_baseEmbedding, ← IsScalarTower.algebraMap_apply]
    exact hrd'
  have hca : IsCMField.complexConj (modelField p Ω N F.Carrier) ⟨xa, hxaE⟩ = -⟨xa, hxaE⟩ := by
    apply injE
    rw [algebraMap_complexConj (M := N), map_neg]
    exact conjQ_of_sq_neg ha hxa
  have hcd : IsCMField.complexConj (modelField p Ω N F.Carrier) ⟨xd, hxdE⟩ = ⟨xd, hxdE⟩ := by
    apply injE
    rw [algebraMap_complexConj (M := N)]
    exact (conjQ_eq_self_iff xd).mpr (mem_maximalRealSubfield_of_sq_pos hd hxd)
  have hta : t ⟨xa, hxaE⟩ = ⟨xa, hxaE⟩ := injE (by rw [ht]; exact hsa)
  have htd : t ⟨xd, hxdE⟩ = -⟨xd, hxdE⟩ := injE (by rw [ht, map_neg]; exact hsd)
  -- Degrees and the four places.
  obtain ⟨hdeg, hdegL, hNC⟩ := harrisDegrees F F' jE' jL hE' hcE' θ hθ
  obtain ⟨P, Ps, φ, φs, hrest⟩ :=
    pairedPlaces_of_embeddings F F' jE jE' jL hE hE' hL hcE hcE' θ hθ t t' tL hsE hsE' hsσ
      (IsCMField.complexConj (topModel p Ω N F.Carrier (galoisClosure F F').field)).toRingEquiv
      hc hjxa hjxd (fun h => hxa0 (congrArg Subtype.val h))
      (fun h => hxd0 (congrArg Subtype.val h)) hca hcd hta htd
  exact ⟨modelField p Ω N F.Carrier, topModel p Ω N F.Carrier F'.field,
    topModel p Ω N F.Carrier (galoisClosure F F').field, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hCM, hCM', hCML, inferInstance,
    inferInstance, inferInstance, inferInstance, hNC, _, P, Ps, φ, φs, θ, hK₀, hsup, hsup',
    hsupL, hdeg, hdegL, hrest⟩

end Langlands.Global.CMRealization
