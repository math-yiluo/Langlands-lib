import Langlands.GroupScheme.Reductive.GeometricReductivityShift
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.Unipotent.PrimitiveCoordinate
import Langlands.GroupScheme.Unipotent.AdditiveCharacter
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Rational.CharacterLatticeProof

/-! # Shifted coordinates of corepresented groups from point identities -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.AdditiveShift

open AffineLinearEmbedding
open Algebra.TensorProduct (includeLeft includeRight productMap)

variable {K : Type u} [Field K] {F : CommAlgCat.{u} (CommRingCat.of K) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of K)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- Pulling back global functions along the spectrum of an algebra map. -/
theorem appTop_algSpec_map {S S' : CommAlgCat.{u} (CommRingCat.of K)} (f : S →ₐ[CommRingCat.of K] S')
    (s : S) :
    ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op).left.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) =
      (Scheme.ΓSpecIso (CommRingCat.of S')).inv (f s) := by
  have h := congrArg (fun φ => φ.hom s)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (f : S →+* S')))
  exact h.symm

/-- Evaluation at the point classified by an algebra map. -/
theorem evalAt_algSpec_map {S : CommAlgCat.{u} (CommRingCat.of K)}
    (f : B →ₐ[CommRingCat.of K] S) (b : B) :
    evalAt e ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op) b =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (f b) := by
  exact (evalAt_apply e ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op) b).trans
    (appTop_algSpec_map f b)

/-- Evaluation is natural in the test scheme. -/
theorem evalAt_comp {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (Corepresented.groupScheme F e).X) (b : B) :
    evalAt e (a ≫ x) b = a.left.appTop (evalAt e x b) := by
  rw [evalAt_apply, evalAt_apply, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

/-- Evaluation at a product of points is convolution through the comultiplication. -/
theorem evalAt_mul {T : Over (Spec (CommRingCat.of K))}
    (x y : T ⟶ (Corepresented.groupScheme F e).X) :
    evalAt e (x * y) = (productMap (evalAt e x) (evalAt e y)).comp (comul e) := by
  rw [evalAt, map_mul, homEquiv_symm_mul]

/-- The algebra map classifying an affine point of the corepresented group. -/
abbrev affineCls {S : CommAlgCat.{u} (CommRingCat.of K)}
    (x : (algSpec (CommRingCat.of K)).obj (op S) ⟶ (Corepresented.groupScheme F e).X) :
    B →ₐ[CommRingCat.of K] S :=
  (e.homEquiv.symm (Corepresented.affinePointsEquiv F e S x)).hom

theorem affineCls_map {S : CommAlgCat.{u} (CommRingCat.of K)} (f : B →ₐ[CommRingCat.of K] S) :
    affineCls e ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op) = f := by
  show (e.homEquiv.symm (Corepresented.affinePointsEquiv F e S _)).hom = f
  rw [Corepresented.affinePointsEquiv_map, Equiv.symm_apply_apply]
  rfl

theorem affineCls_comp {S S' : CommAlgCat.{u} (CommRingCat.of K)}
    (g : S →ₐ[CommRingCat.of K] S')
    (x : (algSpec (CommRingCat.of K)).obj (op S) ⟶ (Corepresented.groupScheme F e).X) :
    affineCls e ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom g).op ≫ x) =
      g.comp (affineCls e x) := by
  show (e.homEquiv.symm (Corepresented.affinePointsEquiv F e S' _)).hom = _
  rw [Corepresented.affinePointsEquiv_naturality, homEquiv_symm_map]
  rfl

theorem eq_algSpec_map_affineCls {S : CommAlgCat.{u} (CommRingCat.of K)}
    (x : (algSpec (CommRingCat.of K)).obj (op S) ⟶ (Corepresented.groupScheme F e).X) :
    x = (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (affineCls e x)).op := by
  apply (Corepresented.affinePointsEquiv F e S).injective
  rw [Corepresented.affinePointsEquiv_map, CommAlgCat.ofHom_hom, Equiv.apply_symm_apply]

/-- Evaluation at an affine point is its classifying algebra map, read in global sections. -/
theorem evalAt_affine {S : CommAlgCat.{u} (CommRingCat.of K)}
    (x : (algSpec (CommRingCat.of K)).obj (op S) ⟶ (Corepresented.groupScheme F e).X) (b : B) :
    evalAt e x b = (Scheme.ΓSpecIso (CommRingCat.of S)).inv (affineCls e x b) := by
  conv_lhs => rw [eq_algSpec_map_affineCls e x]
  exact evalAt_algSpec_map e (affineCls e x) b

variable {F' : CommAlgCat.{u} (CommRingCat.of K) ⥤ GrpCat.{u}}
  {C' : CommAlgCat.{u} (CommRingCat.of K)} (e' : (F' ⋙ forget GrpCat).CorepresentableBy C')

/-- A point identity `h(n x) = h(x) + c(n)` on all test schemes gives the tensor shift identity
for the algebra map classifying `j`. -/
theorem isShift_of_points
    (j : Corepresented.groupScheme F' e' ⟶ Corepresented.groupScheme F e) (h : B) (c : C')
    (hpt : ∀ (T : Over (Spec (CommRingCat.of K)))
      (n : T ⟶ (Corepresented.groupScheme F' e').X) (x : T ⟶ (Corepresented.groupScheme F e).X),
      evalAt e ((n ≫ j.hom.hom) * x) h = evalAt e x h + evalAt e' n c) :
    letI := bialgebra e
    IsShift (affineCls e (S := C') j.hom.hom) c h 1 := by
  let := bialgebra e
  let φ : B →ₐ[K] C' := affineCls e (S := C') j.hom.hom
  let A : CommAlgCat.{u} (CommRingCat.of K) := CommAlgCat.of (CommRingCat.of K) (C' ⊗[K] B)
  let n₀ : (algSpec (CommRingCat.of K)).obj (op A) ⟶ (Corepresented.groupScheme F' e').X :=
    (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (includeLeft : C' →ₐ[K] C' ⊗[K] B)).op
  let x₀ : (algSpec (CommRingCat.of K)).obj (op A) ⟶ (Corepresented.groupScheme F e).X :=
    (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (includeRight : B →ₐ[K] C' ⊗[K] B)).op
  let sec : A →+* ((algΓ (CommRingCat.of K)).obj ((algSpec (CommRingCat.of K)).obj (op A))).unop :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hsec : Function.Injective sec :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.injective
  have hx₀ : ∀ b : B, evalAt e x₀ b = sec ((1 : C') ⊗ₜ[K] b) := fun b =>
    evalAt_algSpec_map e (S := A) (includeRight : B →ₐ[K] C' ⊗[K] B) b
  have hN₀ : evalAt e' n₀ c = sec (c ⊗ₜ[K] 1) :=
    evalAt_algSpec_map e' (S := A) (includeLeft : C' →ₐ[K] C' ⊗[K] B) c
  have hj₀ : ∀ b : B, evalAt e (n₀ ≫ j.hom.hom) b = sec (φ b ⊗ₜ[K] 1) := by
    intro b
    have h2 : affineCls e (n₀ ≫ j.hom.hom) b = φ b ⊗ₜ[K] (1 : B) :=
      congrArg (fun g => g b)
        (affineCls_comp e (S := C') (S' := A) (includeLeft : C' →ₐ[K] C' ⊗[K] B) j.hom.hom)
    exact (evalAt_affine e (S := A) _ b).trans (congrArg sec h2)
  have hprod : ∀ t : B ⊗[K] B,
      productMap (evalAt e (n₀ ≫ j.hom.hom)) (evalAt e x₀) t =
        sec ((φ.toLinearMap.rTensor B) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul p q =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, hj₀, hx₀, ← map_mul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  have key := hpt _ n₀ x₀
  rw [evalAt_mul, AlgHom.comp_apply, hprod, hx₀, hN₀, ← map_add] at key
  have hcomul : (Coalgebra.comul (R := K) h : B ⊗[K] B) = comul e h := rfl
  unfold IsShift
  rw [hcomul, one_smul]
  exact hsec key

end Langlands.GroupScheme.AdditiveShift

namespace Langlands.GroupScheme.AdditiveShift

open AffineLinearEmbedding
open Algebra.TensorProduct (includeLeft includeRight productMap)

variable {K : Type u} [Field K]

/-- Over an algebraically closed field, a pseudo-reductive group `G` admits no function `f` with
`f(n x) = f(x) + χ(n)` for a nontrivial smooth connected unipotent group `N ⟶ G`, as soon as such
functions exist for every additive function `χ` on the points of `N`. The hypothesis `hcoc` is
supplied by the affineness of the quotient by `N`. -/
theorem false_of_shift_functions [IsAlgClosed K] (hHab : ReductiveGeometricReductivityStatement.{u})
    {G N : GroupScheme (Spec (CommRingCat.of K))} (hG : IsPseudoReductive G)
    [IsAffine N.X.left] [Smooth N.X.hom] [ConnectedSpace N.X.left] (hU : IsUnipotent N)
    (j : N ⟶ G) (hnt : ∃ (T : Over (Spec (CommRingCat.of K))) (n : T ⟶ N.X), n ≠ 1)
    (hcoc : ∀ (χ : ∀ {T : Over (Spec (CommRingCat.of K))}, (T ⟶ N.X) → Γ(T.left, ⊤)),
      (∀ {T T' : Over (Spec (CommRingCat.of K))} (t : T' ⟶ T) (n : T ⟶ N.X),
        χ (t ≫ n) = t.left.appTop (χ n)) →
      (∀ {T : Over (Spec (CommRingCat.of K))} (n m : T ⟶ N.X), χ (n * m) = χ n + χ m) →
      ∃ f : Γ(G.X.left, ⊤), ∀ (T : Over (Spec (CommRingCat.of K))) (n : T ⟶ N.X)
        (x : T ⟶ G.X), ((n ≫ j.hom.hom) * x).left.appTop f = x.left.appTop f + χ n) :
    False := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let eG := AffineCoordinates.groupSchemeIso G
  let eN := AffineCoordinates.groupSchemeIso N
  let cG := AffineCoordinates.corepresentation G
  let cN := AffineCoordinates.corepresentation N
  let C' := AffineCoordinates.algebra N
  let := bialgebra cN
  -- a nonconstant primitive coordinate of `N`
  have hU' := IsUnipotent.of_iso eN hU
  have hconst : ∃ a : C', a ∉ K ∙ (1 : C') := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    have hbot := Unipotent.range_id_eq_bot_of_all_mem_constants cN hc
    obtain ⟨T, n, hn⟩ := hnt
    apply hn
    have hmem : n ≫ eN.inv.hom.hom ∈
        (SubgroupFunctor.range (𝟙 (Corepresented.groupScheme _ cN))).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨n ≫ eN.inv.hom.hom, by rw [Grp.id_hom_hom, Category.comp_id]⟩
    rw [hbot] at hmem
    have h1 : n ≫ eN.inv.hom.hom = 1 := hmem
    calc n = (n ≫ eN.inv.hom.hom) ≫ eN.hom.hom.hom := by
          rw [Category.assoc, ← Grp.comp_hom_hom, eN.inv_hom_id, Grp.id_hom_hom,
            Category.comp_id]
      _ = 1 := by rw [h1, MonObj.one_comp]
  obtain ⟨b, hb0, hbprim⟩ :=
    Unipotent.exists_nonzero_primitive_of_oneMemStable
      (Unipotent.oneMemStable_of_isUnipotent cN hU') hconst
  have hbcomul : comul cN b = 1 ⊗ₜ[K] b + b ⊗ₜ[K] 1 :=
    Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mp hbprim
  -- the additive function on points of `N` given by the primitive coordinate
  let χ : ∀ {T : Over (Spec (CommRingCat.of K))}, (T ⟶ N.X) → Γ(T.left, ⊤) :=
    fun n => evalAt cN (n ≫ eN.inv.hom.hom) b
  have hχnat : ∀ {T T' : Over (Spec (CommRingCat.of K))} (t : T' ⟶ T) (n : T ⟶ N.X),
      χ (t ≫ n) = t.left.appTop (χ n) := by
    intro T T' t n
    change evalAt cN ((t ≫ n) ≫ eN.inv.hom.hom) b = t.left.appTop (evalAt cN (n ≫ eN.inv.hom.hom) b)
    rw [Category.assoc, evalAt_comp]
  have hχadd : ∀ {T : Over (Spec (CommRingCat.of K))} (n m : T ⟶ N.X),
      χ (n * m) = χ n + χ m := by
    intro T n m
    change evalAt cN ((n * m) ≫ eN.inv.hom.hom) b =
      evalAt cN (n ≫ eN.inv.hom.hom) b + evalAt cN (m ≫ eN.inv.hom.hom) b
    rw [MonObj.mul_comp, evalAt_mul, AlgHom.comp_apply, hbcomul, map_add,
      Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, map_one, one_mul, mul_one, add_comm]
  obtain ⟨f, hf⟩ := hcoc χ hχnat hχadd
  -- transport the shifted function to the corepresented model of `G`
  let B := AffineCoordinates.algebra G
  let hB : B := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    (show Γ(Spec (CommRingCat.of B), ⊤) from eG.hom.hom.hom.left.appTop f)
  have hev : ∀ {T : Over (Spec (CommRingCat.of K))}
      (y : T ⟶ (Corepresented.groupScheme _ cG).X),
      evalAt cG y hB = (y ≫ eG.hom.hom.hom).left.appTop f := by
    intro T y
    rw [evalAt_apply, Iso.hom_inv_id_apply, Over.comp_left, Scheme.Hom.comp_appTop]
    rfl
  let j' : Corepresented.groupScheme _ cN ⟶ Corepresented.groupScheme _ cG :=
    eN.hom ≫ j ≫ eG.inv
  have hpt : ∀ (T : Over (Spec (CommRingCat.of K)))
      (n : T ⟶ (Corepresented.groupScheme _ cN).X) (x : T ⟶ (Corepresented.groupScheme _ cG).X),
      evalAt cG ((n ≫ j'.hom.hom) * x) hB = evalAt cG x hB + evalAt cN n b := by
    intro T n x
    rw [hev, hev, MonObj.mul_comp]
    have hj : (n ≫ j'.hom.hom) ≫ eG.hom.hom.hom = (n ≫ eN.hom.hom.hom) ≫ j.hom.hom := by
      simp only [j', Grp.comp_hom_hom, Category.assoc]
      rw [← Grp.comp_hom_hom, eG.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
    rw [hj, hf]
    congr 1
    change evalAt cN ((n ≫ eN.hom.hom.hom) ≫ eN.inv.hom.hom) b = _
    rw [Category.assoc, ← Grp.comp_hom_hom, eN.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  have hshift := isShift_of_points cG cN j' hB b hpt
  -- the coordinate ring of `N` is a domain
  have : IsLocallyNoetherian N.X.left := LocallyOfFiniteType.isLocallyNoetherian N.X.hom
  have : IsIntegral N.X.left := CharacterLatticeProof.isIntegral_of_smooth K N.X.hom
  let eS : (Corepresented.groupScheme _ cN).X.left ≅ N.X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso eN)
  have : IsIntegral (Corepresented.groupScheme _ cN).X.left := IsIntegral.of_isIso eS.inv
  have hdomΓ : IsDomain Γ((Corepresented.groupScheme _ cN).X.left, ⊤) := inferInstance
  have : IsDomain C' :=
    @MulEquiv.isDomain _ _ _ _ hdomΓ
      (Scheme.ΓSpecIso (CommRingCat.of C')).commRingCatIsoToRingEquiv.symm.toMulEquiv
  -- the primitive coordinate is not a scalar
  have hψ : b ∉ Set.range (algebraMap K C') := by
    rintro ⟨c, hc⟩
    have hε : counit (R := K) b = 0 := hbprim.counit_eq_zero
    rw [← hc, Bialgebra.counit_algebraMap] at hε
    exact hb0 (by rw [← hc, hε, map_zero])
  have hGR := (isGeometricallyReductive_of_statement hHab hG).of_iso eG
  exact false_of_isShift cG hGR (affineCls cG (S := C') j'.hom.hom) b hψ hB hshift

end Langlands.GroupScheme.AdditiveShift
