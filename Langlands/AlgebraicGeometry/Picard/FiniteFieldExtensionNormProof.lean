import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormGluing
import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormStatement
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-! # Norms of functions along the base change of a finite field extension (proof) -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

namespace FiniteFieldExtensionNorm

open Module

/-! ## Algebraic lemmas on norms of finite free algebras -/

section Algebra

variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B'] {ι : Type*} [Fintype ι]

/-- A ring map sending a basis to a basis, compatibly with a map of base rings, maps
coordinates to coordinates. -/
theorem basis_repr_map (b : Basis ι A B) (b' : Basis ι A' B') (σ : A →+* A') (φ : B →+* B')
    (hφ : ∀ a, φ (algebraMap A B a) = algebraMap A' B' (σ a)) (hb : ∀ i, φ (b i) = b' i)
    (y : B) (i : ι) : b'.repr (φ y) i = σ (b.repr y i) := by
  classical
  have h : φ y = ∑ j, σ (b.repr y j) • b' j := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, hb]
  rw [h, b'.repr_sum_self]

/-- The norm commutes with ring maps sending a basis to a basis. -/
theorem norm_map_of_basis (b : Basis ι A B) (b' : Basis ι A' B') (σ : A →+* A') (φ : B →+* B')
    (hφ : ∀ a, φ (algebraMap A B a) = algebraMap A' B' (σ a)) (hb : ∀ i, φ (b i) = b' i)
    (f : B) : σ (Algebra.norm A f) = Algebra.norm A' (φ f) := by
  classical
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [← hb j, ← map_mul, basis_repr_map b b' σ φ hφ hb]

/-- In a finite free algebra, every element divides the image of its norm. -/
theorem dvd_algebraMap_norm [Module.Free A B] [Module.Finite A B] (f : B) :
    f ∣ algebraMap A B (Algebra.norm A f) := by
  set P := (Algebra.lmul A B f).charpoly
  have h0 : Polynomial.aeval f P = 0 := Algebra.aeval_self_charpoly_lmul f
  rw [← Polynomial.X_mul_divX_add P, map_add, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hc : algebraMap A B (P.coeff 0) = f * -(Polynomial.aeval f P.divX) := by
    rw [mul_neg, eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, hc]
  exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

/-- If an element of a free algebra with a finite basis lies in a prime, its norm lies in the
contraction of that prime. -/
theorem norm_mem_comap (b : Basis ι A B) (f : B) (Q : Ideal B) (hf : f ∈ Q) :
    Algebra.norm A f ∈ Q.comap (algebraMap A B) := by
  have : Module.Free A B := Module.Free.of_basis b
  have : Module.Finite A B := Module.Finite.of_basis b
  obtain ⟨g, hg⟩ := dvd_algebraMap_norm (A := A) f
  rw [Ideal.mem_comap, hg]
  exact Q.mul_mem_right _ hf

/-- If the norm of an element of a free algebra with a finite basis lies in a prime `P`, then
some prime lying over `P` contains the element. -/
theorem exists_prime_over_of_norm_mem (b : Basis ι A B) (f : B) (P : Ideal A) [P.IsPrime]
    (hf : Algebra.norm A f ∈ P) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap (algebraMap A B) = P ∧ f ∈ Q := by
  have : Module.Finite A B := Module.Finite.of_basis b
  have hIP : (Ideal.span {f}).under A ≤ P := by
    intro a ha
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp ha)
    have : a ^ Fintype.card ι ∈ P := by
      rw [← Algebra.norm_algebraMap_of_basis b, ← hg, map_mul]
      exact P.mul_mem_left _ hf
    exact ‹P.IsPrime›.mem_of_pow_mem _ this
  obtain ⟨Q, hQI, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (Ideal.span {f}) hIP
  exact ⟨Q, hQ, hQP, hQI (Ideal.subset_span rfl)⟩

end Algebra

/-! ## The base change over an affine open -/

section Affine

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

variable (K L) in
/-- The morphism `Spec L ⟶ Spec K` along which we base change. -/
noncomputable abbrev bc : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- Composites of restriction maps of a presheaf on opens only depend on source and target. -/
theorem map_comp_map_eq {C : Type*} [Category C] {T : Type*} [TopologicalSpace T]
    (F : (Opens T)ᵒᵖ ⥤ C) {R : C} {U V W : (Opens T)ᵒᵖ} (a : R ⟶ F.obj U) (f : U ⟶ V)
    (g : V ⟶ W) (h : U ⟶ W) : (a ≫ F.map f) ≫ F.map g = a ≫ F.map h := by
  rw [Category.assoc, ← F.map_comp]
  rfl

/-- A restriction map followed by a restriction map back is the identity. -/
theorem map_comp_map_self {C : Type*} [Category C] {T : Type*} [TopologicalSpace T]
    (F : (Opens T)ᵒᵖ ⥤ C) {R : C} {U V : (Opens T)ᵒᵖ} (a : R ⟶ F.obj U) (f : U ⟶ V)
    (g : V ⟶ U) : (a ≫ F.map f) ≫ F.map g = a := by
  rw [map_comp_map_eq F a f g (𝟙 U), F.map_id, Category.comp_id]

variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

/-- The `K`-structure map on sections of `X` over an open. -/
noncomputable def coefX (V : X.Opens) : CommRingCat.of K ⟶ Γ(X, V) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop ≫ X.presheaf.map (homOfLE le_top).op

variable (L) in
/-- The `L`-structure map on sections of `X_L` over the preimage of an open of `X`. -/
noncomputable def coefXL (V : X.Opens) :
    CommRingCat.of L ⟶ Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (pullback.snd p (bc K L)).appTop ≫
    (pullback p (bc K L)).presheaf.map (homOfLE le_top).op

variable (L) in
/-- Over an affine open `V` of `X`, the sections of `X_L` over `π⁻¹ V` are the pushout of
`Γ(X, V)` and `L` over `K`. -/
theorem isPushout_affine (V : X.Opens) (hV : IsAffineOpen V) :
    IsPushout (coefX p V) (CommRingCat.ofHom (algebraMap K L))
      ((pullback.fst p (bc K L)).app V) (coefXL L p V) := by
  have : IsAffine V := hV
  have h := (isPullback_morphismRestrict (pullback.fst p (bc K L)) V).paste_vert
    (IsPullback.of_hasPullback p (bc K L))
  refine (isPushout_appTop_of_isPullback h).of_iso (Scheme.ΓSpecIso _) V.topIso
    (Scheme.ΓSpecIso _) (pullback.fst p (bc K L) ⁻¹ᵁ V).topIso ?_ ?_ ?_ ?_
  · simp only [coefX, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
      Iso.hom_inv_id_assoc]
    exact map_comp_map_eq X.presheaf _ _ _ _
  · exact Scheme.ΓSpecIso_naturality _
  · rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv]
    exact (Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (map_comp_map_self (pullback p (bc K L)).presheaf _ _ _))
  · simp only [coefXL, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
      Iso.hom_inv_id_assoc]
    exact map_comp_map_eq (pullback p (bc K L)).presheaf _ _ _ _

variable (L) in
/-- Over an affine open `V` of `X`, the sections of `X_L` over `π⁻¹ V` are free over `Γ(X, V)`,
with a basis given by the image of a `K`-basis of `L`. -/
theorem exists_basis [FiniteDimensional K L] (V : X.Opens) (hV : IsAffineOpen V) :
    letI := ((pullback.fst p (bc K L)).app V).hom.toAlgebra
    ∃ bB : Basis (Fin (finrank K L)) Γ(X, V)
        Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V),
      ∀ i, bB i = (coefXL L p V).hom (Module.finBasis K L i) := by
  let : Algebra Γ(X, V) Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    ((pullback.fst p (bc K L)).app V).hom.toAlgebra
  let : Algebra K Γ(X, V) := (coefX p V).hom.toAlgebra
  let : Algebra L Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    (coefXL L p V).hom.toAlgebra
  let : Algebra K Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    ((coefXL L p V).hom.comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower K Γ(X, V) Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (isPushout_affine L p V hV).w).symm
  have : Algebra.IsPushout K Γ(X, V) L
      Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_affine L p V hV)
  exact ⟨Algebra.IsPushout.out.basis (Module.finBasis K L),
    fun i => IsBaseChange.basis_apply _ _ _⟩

variable (L) in
/-- The norm over an open `V` of `X`: the determinant of multiplication on the sections of `X_L`
over `π⁻¹ V`, viewed as a `Γ(X, V)`-algebra. It is the intended norm when `V` is affine. -/
noncomputable def normAff (V : X.Opens) :
    Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) →* Γ(X, V) :=
  letI := ((pullback.fst p (bc K L)).app V).hom.toAlgebra
  Algebra.norm Γ(X, V)

variable (L) in
/-- The norm over affine opens commutes with restriction to smaller affine opens. -/
theorem normAff_res [FiniteDimensional K L] {V V' : X.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V)
    (f : Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V)) :
    X.presheaf.map (homOfLE h).op (normAff L p V f) =
      normAff L p V' ((pullback p (bc K L)).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono (pullback.fst p (bc K L)) h)).op f) := by
  let : Algebra Γ(X, V) Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    ((pullback.fst p (bc K L)).app V).hom.toAlgebra
  let : Algebra Γ(X, V') Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V') :=
    ((pullback.fst p (bc K L)).app V').hom.toAlgebra
  obtain ⟨bB, hbB⟩ := exists_basis L p V hV
  obtain ⟨bB', hbB'⟩ := exists_basis L p V' hV'
  refine norm_map_of_basis bB bB' (X.presheaf.map (homOfLE h).op).hom
    ((pullback p (bc K L)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono (pullback.fst p (bc K L)) h)).op).hom ?_ ?_ f
  · intro a
    exact congr($((pullback.fst p (bc K L)).naturality (homOfLE h).op).hom a).symm
  · intro i
    rw [hbB, hbB']
    exact congr($(map_comp_map_eq (pullback p (bc K L)).presheaf
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (pullback.snd p (bc K L)).appTop) _ _ _).hom
      (Module.finBasis K L i))

variable (L) in
/-- The norm over an affine open raises functions pulled back from `X` to the power `[L : K]`. -/
theorem normAff_app [FiniteDimensional K L] {V : X.Opens} (hV : IsAffineOpen V) (g : Γ(X, V)) :
    normAff L p V ((pullback.fst p (bc K L)).app V g) = g ^ finrank K L := by
  let : Algebra Γ(X, V) Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    ((pullback.fst p (bc K L)).app V).hom.toAlgebra
  obtain ⟨bB, -⟩ := exists_basis L p V hV
  rw [← Fintype.card_fin (finrank K L)]
  exact Algebra.norm_algebraMap_of_basis bB g


set_option backward.isDefEq.respectTransparency.types false in
/-- The first projection `X_L ⟶ X` is an affine morphism. -/
instance isAffineHom_fst : IsAffineHom (pullback.fst p (bc K L)) := by
  have : IsAffineHom (bc K L) := inferInstance
  exact MorphismProperty.pullback_fst _ _ this

omit [Algebra K L] in
/-- A point of an affine open, given by a prime of its ring of sections, lies in the basic open of
a section iff the section is not in the prime. -/
theorem fromSpec_mem_basicOpen {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U) (a : Γ(Y, U))
    (P : PrimeSpectrum Γ(Y, U)) : hU.fromSpec P ∈ Y.basicOpen a ↔ a ∉ P.asIdeal := by
  change P ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen a ↔ _
  rw [hU.fromSpec_preimage_basicOpen]
  rfl

variable (L) in
/-- Over an affine open, a point lies in the basic open of the norm of `f` iff its whole fibre
lies in the basic open of `f`. -/
theorem mem_basicOpen_normAff [FiniteDimensional K L] {V : X.Opens} (hV : IsAffineOpen V)
    (f : Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V)) (x : X) (hx : x ∈ V) :
    x ∈ X.basicOpen (normAff L p V f) ↔
      ∀ y : (pullback p (bc K L) : Scheme.{u}), (pullback.fst p (bc K L)).base y = x →
        y ∈ (pullback p (bc K L)).basicOpen f := by
  let : Algebra Γ(X, V) Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V) :=
    ((pullback.fst p (bc K L)).app V).hom.toAlgebra
  obtain ⟨bB, -⟩ := exists_basis L p V hV
  have hW : IsAffineOpen (pullback.fst p (bc K L) ⁻¹ᵁ V) := hV.preimage _
  have hcomap : ∀ Q : Spec Γ(pullback p (bc K L), pullback.fst p (bc K L) ⁻¹ᵁ V),
      (pullback.fst p (bc K L)).base (hW.fromSpec Q) =
        hV.fromSpec (Spec.map ((pullback.fst p (bc K L)).app V) Q) := by
    intro Q
    rw [Scheme.Hom.app_eq_appLE]
    exact congr($(IsAffineOpen.SpecMap_appLE_fromSpec (pullback.fst p (bc K L)) hV hW
      le_rfl).base Q).symm
  constructor
  · intro hN y hy
    have hyW : y ∈ pullback.fst p (bc K L) ⁻¹ᵁ V := by
      change (pullback.fst p (bc K L)).base y ∈ V
      rw [hy]; exact hx
    obtain ⟨Q, rfl⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    refine (fromSpec_mem_basicOpen hW f Q).mpr fun hfQ => ?_
    rw [← hy, hcomap] at hN
    exact (fromSpec_mem_basicOpen hV _ _).mp hN (norm_mem_comap bB f _ hfQ)
  · intro hy
    obtain ⟨P, rfl⟩ : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
    refine (fromSpec_mem_basicOpen hV _ P).mpr fun hNP => ?_
    have : (PrimeSpectrum.asIdeal P).IsPrime := PrimeSpectrum.isPrime P
    obtain ⟨Q, hQ, hQP, hfQ⟩ := exists_prime_over_of_norm_mem bB f (PrimeSpectrum.asIdeal P) hNP
    have hyQ := hy (hW.fromSpec ⟨Q, hQ⟩)
      ((hcomap ⟨Q, hQ⟩).trans (congrArg hV.fromSpec (PrimeSpectrum.ext hQP)))
    exact (fromSpec_mem_basicOpen hW f ⟨Q, hQ⟩).mp hyQ hfQ

end Affine

end FiniteFieldExtensionNorm

open FiniteFieldExtensionNorm in
/-- The norm of functions along the base change `X_L ⟶ X` of a finite field extension `L / K`:
the affine norms `normAff` glue to all opens of `X`. -/
theorem finiteFieldExtensionNorm : FiniteFieldExtensionNormStatement.{u} := by
  intro K L _ _ _ _ X p
  refine ⟨AffineNormGluing.norm (pullback.fst p (bc K L)) (fun V => normAff L p V)
    (fun U V hUV f => normAff_res L p V.2 U.2 hUV f), ?_, ?_, ?_⟩
  · exact AffineNormGluing.naturality _ _ _
  · exact AffineNormGluing.degree _ _ _ _ fun V g => normAff_app L p V.2 g
  · refine AffineNormGluing.basicOpen _ _ _ fun V f => Set.ext fun x => ⟨fun h => ?_, ?_⟩
    · have hx : x ∈ (V : X.Opens) := X.basicOpen_le _ h
      exact ⟨hx, (mem_basicOpen_normAff L p V.2 f x hx).mp h⟩
    · rintro ⟨hx, h⟩
      exact (mem_basicOpen_normAff L p V.2 f x hx).mpr h

end Langlands.AlgebraicGeometry.Picard
