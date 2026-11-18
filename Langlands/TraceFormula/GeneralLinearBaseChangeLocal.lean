import Langlands.Global.LocalModularCharacter.HaarScaleNorm
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Global.AdelicLocalCharacterNorm
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.LinearIntegralFamily
import Langlands.TraceFormula.AdelicGroupAutomorphism
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.AffineWeilUnitGalois
import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.GeneralLinearPointTopology
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.Group.GL.IntegralSubgroup
import Langlands.BaseChange.Norm
import Langlands.Global.IntegralFiniteAdeles
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Local components of `Res_{L/K} GL_n` at a place of `K`

The local algebra `E_i = K_i ⊗_K L` with `σ_i = id ⊗ σ`, the identification
`W(K_i) ≃ GL_n(E_i)` for `W = Res_{L/K} GL_n` with its compatibility with the twist, the unit
and the norm, the integral subgroups at the finite places, and restricted tensor products of
adelic functions.  See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped TensorProduct CategoryTheory.MonObj Topology
open Langlands.Global Langlands.GroupScheme Langlands.BaseChange
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

/-- A finite basis identifies the module topology with the product topology on coefficients. -/
private def basisHomeomorph {R M J : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsModuleTopology R M] [Fintype J] (b : Module.Basis J R M) : M ≃ₜ (J → R) where
  toEquiv := b.equivFun.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  continuous_invFun := by
    let := IsModuleTopology.toContinuousAdd R M
    exact IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap

open Langlands.Algebra Langlands.AlgebraicGeometry.PointTopology in
set_option backward.isDefEq.respectTransparency false in
/-- On each section the Weil comparison evaluates a tensor with finitely many terms. -/
private theorem continuous_affineWeilPointsEquiv
    (A B T : Type u) [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]
    [Module.Finite A B] [Module.Projective A B]
    (G : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [TopologicalSpace T] [TopologicalSpace (B ⊗[A] T)] [ContinuousAdd (B ⊗[A] T)]
    (h : ∀ b : B, Continuous (fun t : T => b ⊗ₜ[A] t)) :
    Continuous[(AffineWeil.groupScheme A B G).affinePointsTopologicalSpace (CommAlgCat.of A T),
      G.affinePointsTopologicalSpace (CommAlgCat.of B (B ⊗[A] T))]
      (AffineWeil.pointsEquiv A B G T) := by
  let D := WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X)
  let W := AffineWeil.groupScheme A B G
  let S := CommAlgCat.of A T
  let : TopologicalSpace (W.affinePoints S) := W.affinePointsTopologicalSpace S
  let q : W.affinePoints S → AlgPoint A D T :=
    (spectrumAlgebraPointHomeomorph A T D) ∘ (W.affinePointsRingPointHomeomorph S)
  have hq : Continuous q :=
    (spectrumAlgebraPointHomeomorph A T D).continuous.comp
      (W.affinePointsRingPointHomeomorph S).continuous
  have hcoords (p : W.affinePoints S) : (q p).toAlgHom = affineRingPointEquiv A D T p := by
    change (spectrumAlgebraPointHomeomorph A T D (W.affinePointsRingPointHomeomorph S p)).toAlgHom = _
    rw [W.affinePointsRingPointHomeomorph_apply]
    rfl
  have htensor (z : B ⊗[A] D) :
      Continuous (fun p : W.affinePoints S =>
        Algebra.TensorProduct.lTensor (S := B) B (q p).toAlgHom z) := by
    induction z using TensorProduct.inductionOn with
    | tmul b d =>
      change Continuous (fun p : W.affinePoints S => b ⊗ₜ[A] (q p) d)
      exact (h b).comp ((AlgPoint.continuous_eval d).comp hq)
    | add z w hz hw =>
      simp only [map_add]
      exact hz.add hw
  apply (G.continuous_affinePoints_iff (CommAlgCat.of B (B ⊗[A] T)) _).mpr
  intro c
  have heval (p : W.affinePoints S) :
      G.affinePointEvaluation (CommAlgCat.of B (B ⊗[A] T)) (AffineWeil.pointsEquiv A B G T p) c =
        Algebra.TensorProduct.lTensor (S := B) B (q p).toAlgHom
          (WeilRestrictionFiniteType.universalPoint A B (AffineCoordinateRing B G.X) c) := by
    rw [← G.affineSchemePointEquiv_evaluation, ← AlgPoint.toAlgHom_apply,
      AffineWeil.pointsEquiv_coordinates, WeilRestrictionFiniteType.homEquiv_apply, hcoords]
    rfl
  simp_rw [heval]
  exact htensor _

local instance generalLinearBaseChangeLocalIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearBaseChangeLocalSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

variable (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [Algebra K L]

/-- The completion `K_i` at a place `i` of `K` as a field, extending its ring structure. -/
@[instance_reducible]
def placeCompletionField (i : Place K) : Field (placeCompletion K i) :=
  (Langlands.Global.placeCompletion.isField K i).toField

namespace PlaceCompletion

/-- The field structure `placeCompletionField` on every completion `K_i`, as an instance
activated by `open scoped Langlands.TraceFormula.PlaceCompletion`.  It is scoped because at a
finite place `v` its inverse is not definitionally the inverse of the field
`v.adicCompletion K`. -/
scoped instance field (i : Place K) : Field (placeCompletion K i) :=
  placeCompletionField K i

end PlaceCompletion

/-- The local algebra `E_i = K_i ⊗_K L` at a place `i` of `K`. -/
def LocalBaseChangeAlgebra (i : Place K) : Type u :=
  placeCompletion K i ⊗[K] L

namespace LocalBaseChangeAlgebra

variable (i : Place K)

instance commRing : CommRing (LocalBaseChangeAlgebra K L i) :=
  inferInstanceAs (CommRing (placeCompletion K i ⊗[K] L))

instance algebra : Algebra (placeCompletion K i) (LocalBaseChangeAlgebra K L i) :=
  inferInstanceAs (Algebra (placeCompletion K i) (placeCompletion K i ⊗[K] L))

instance algebraBase : Algebra K (LocalBaseChangeAlgebra K L i) :=
  inferInstanceAs (Algebra K (placeCompletion K i ⊗[K] L))

instance isScalarTower :
    IsScalarTower K (placeCompletion K i) (LocalBaseChangeAlgebra K L i) :=
  inferInstanceAs (IsScalarTower K (placeCompletion K i) (placeCompletion K i ⊗[K] L))

instance moduleFinite [FiniteDimensional K L] :
    Module.Finite (placeCompletion K i) (LocalBaseChangeAlgebra K L i) :=
  inferInstanceAs (Module.Finite (placeCompletion K i) (placeCompletion K i ⊗[K] L))

/-- The topology of `E_i` as a finite module over the completion `K_i`. -/
instance topologicalSpace : TopologicalSpace (LocalBaseChangeAlgebra K L i) :=
  moduleTopology (placeCompletion K i) (LocalBaseChangeAlgebra K L i)

instance isModuleTopology :
    IsModuleTopology (placeCompletion K i) (LocalBaseChangeAlgebra K L i) :=
  ⟨rfl⟩

instance isTopologicalRing [FiniteDimensional K L] :
    IsTopologicalRing (LocalBaseChangeAlgebra K L i) :=
  IsModuleTopology.isTopologicalRing (placeCompletion K i) (LocalBaseChangeAlgebra K L i)

private def coefficientHomeomorph [FiniteDimensional K L] :
    LocalBaseChangeAlgebra K L i ≃ₜ
      (Module.Free.ChooseBasisIndex K L → placeCompletion K i) :=
  basisHomeomorph (R := placeCompletion K i) (M := LocalBaseChangeAlgebra K L i)
    ((Module.Free.chooseBasis K L).baseChange (placeCompletion K i))

/-- The local algebra is Hausdorff. -/
instance t2Space [FiniteDimensional K L] : T2Space (LocalBaseChangeAlgebra K L i) :=
  (coefficientHomeomorph K L i).symm.t2Space

/-- The local algebra is locally compact. -/
instance locallyCompactSpace [FiniteDimensional K L] :
    LocallyCompactSpace (LocalBaseChangeAlgebra K L i) :=
  (coefficientHomeomorph K L i).locallyCompactSpace_iff.mpr inferInstance

end LocalBaseChangeAlgebra

/-- The automorphism `σ_i = id ⊗ σ` of `E_i = K_i ⊗_K L` over `K_i`. -/
def localGalois (σ : L ≃ₐ[K] L) (i : Place K) :
    LocalBaseChangeAlgebra K L i ≃ₐ[placeCompletion K i] LocalBaseChangeAlgebra K L i :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

theorem localGalois_tmul (σ : L ≃ₐ[K] L) (i : Place K) (x : placeCompletion K i) (y : L) :
    localGalois K L σ i (x ⊗ₜ[K] y) = x ⊗ₜ[K] σ y :=
  rfl

/-- `σ ↦ σ_i` is a group homomorphism `Aut(L/K) →* Aut_{K_i}(E_i)`. -/
def localGaloisHom (i : Place K) :
    (L ≃ₐ[K] L) →* (LocalBaseChangeAlgebra K L i ≃ₐ[placeCompletion K i]
      LocalBaseChangeAlgebra K L i) where
  toFun σ := localGalois K L σ i
  map_one' := Algebra.TensorProduct.congr_refl
  map_mul' σ τ := by
    change Algebra.TensorProduct.congr (AlgEquiv.refl.trans AlgEquiv.refl) (τ.trans σ) =
      (Algebra.TensorProduct.congr AlgEquiv.refl τ).trans
        (Algebra.TensorProduct.congr AlgEquiv.refl σ)
    exact Algebra.TensorProduct.congr_trans _ _ _ _

@[simp] theorem localGaloisHom_apply (σ : L ≃ₐ[K] L) (i : Place K) :
    localGaloisHom K L i σ = localGalois K L σ i :=
  rfl

theorem localGalois_pow (σ : L ≃ₐ[K] L) (i : Place K) (k : ℕ) :
    localGalois K L (σ ^ k) i = localGalois K L σ i ^ k :=
  map_pow (localGaloisHom K L i) σ k

/-- The ring isomorphism `L ⊗_K K_i ≃ E_i` exchanging the factors. -/
def localSwap (i : Place K) : L ⊗[K] placeCompletion K i ≃+* LocalBaseChangeAlgebra K L i :=
  (Algebra.TensorProduct.comm K L (placeCompletion K i)).toRingEquiv

variable [FiniteDimensional K L]

/-- The local points `W(K_i)` of `W = Res_{L/K} GL_n` as `GL_n(E_i)`: the Library's
identification `W(K_i) ≃ GL_n(L ⊗_K K_i)` followed by the exchange of the factors. -/
def localPointsEquiv (n : ℕ) (i : Place K) :
    PlaceGroupPoints K Wₙ i ≃* GL (Fin n) (LocalBaseChangeAlgebra K L i) :=
  (AffineWeil.unitGroundPointsEquiv K L GLₙ (placeCompletion K i)).trans
    ((GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K)
        (CommAlgCat.of K (L ⊗[K] placeCompletion K i))).trans
      (Units.mapEquiv (localSwap K L i).mapMatrix.toMulEquiv))

set_option backward.isDefEq.respectTransparency false in
private theorem continuous_localPointsEquiv (n : ℕ) (i : Place K) :
    Continuous (localPointsEquiv K L n i) := by
  let T : Type u := placeCompletion K i
  let : TopologicalSpace (L ⊗[K] T) := .induced (localSwap K L i) inferInstance
  let : IsTopologicalRing (L ⊗[K] T) :=
    IsTopologicalSemiring.toIsTopologicalRing
      { toContinuousAdd := continuousAdd_induced (localSwap K L i).toRingHom
        toContinuousMul := continuousMul_induced (localSwap K L i) }
  have hswap : Continuous (localSwap K L i) := continuous_induced_dom
  have htensor (b : L) : Continuous (fun t : T => b ⊗ₜ[K] t) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun t : T => localSwap K L i (b ⊗ₜ[K] t))
    have heq (t : T) : localSwap K L i (b ⊗ₜ[K] t) =
        t • (show LocalBaseChangeAlgebra K L i from (1 : T) ⊗ₜ[K] b) := by
      change Algebra.TensorProduct.comm K L T (b ⊗ₜ[K] t) = t • ((1 : T) ⊗ₜ[K] b)
      rw [Algebra.TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp_rw [heq]
    exact continuous_id.smul
      (continuous_const (y := (show LocalBaseChangeAlgebra K L i from (1 : T) ⊗ₜ[K] b)))
  have hweil := continuous_affineWeilPointsEquiv K L T (AffineWeil.unitBaseChange K L GLₙ) htensor
  let S := CommAlgCat.of K (L ⊗[K] T)
  let S' := CommAlgCat.of L (L ⊗[K] T)
  let : TopologicalSpace ((GLₙ).affinePoints S) := (GLₙ).affinePointsTopologicalSpace S
  let : TopologicalSpace ((AffineWeil.unitBaseChange K L GLₙ).affinePoints S') :=
    (AffineWeil.unitBaseChange K L GLₙ).affinePointsTopologicalSpace S'
  have hbase :=
    (affinePointsBaseChangeContinuousMulEquiv K L (L ⊗[K] T) GLₙ).continuous_invFun
  have hgl :=
    (GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K) S).continuous_toFun
  let f : Matrix (Fin n) (Fin n) (L ⊗[K] T) →*
      Matrix (Fin n) (Fin n) (LocalBaseChangeAlgebra K L i) :=
    (localSwap K L i).mapMatrix.toMonoidHom
  have hmatrix : Continuous f :=
    continuous_id.matrix_map
      (f := fun x : L ⊗[K] T => (localSwap K L i x : LocalBaseChangeAlgebra K L i)) hswap
  exact ((hmatrix.units_map f).comp hgl).comp (hbase.comp hweil)

/-- The local points comparison with the evaluation topology on `W(K_i)` and the
matrix-units topology on `GL_n(E_i)`. -/
def localPointsHomeomorph (n : ℕ) (i : Place K) :
    PlaceGroupPoints K Wₙ i ≃ₜ* GL (Fin n) (LocalBaseChangeAlgebra K L i) where
  toMulEquiv := localPointsEquiv K L n i
  continuous_toFun := continuous_localPointsEquiv K L n i
  continuous_invFun := by
    let : SecondCountableTopology (placeCompletion K i) := by
      cases i with
      | inl w => exact infiniteCompletion_secondCountableTopology K w
      | inr v => exact finiteCompletion_secondCountableTopology K v
    let : SecondCountableTopology (PlaceGroupPoints K Wₙ i) :=
      (Wₙ).affinePointsSecondCountableTopology (placeCompletion K i)
    let : LocallyCompactSpace (Matrix (Fin n) (Fin n) (LocalBaseChangeAlgebra K L i)) :=
      inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → LocalBaseChangeAlgebra K L i))
    let : LocallyCompactSpace (GL (Fin n) (LocalBaseChangeAlgebra K L i)) :=
      inferInstanceAs (LocallyCompactSpace (Matrix (Fin n) (Fin n) (LocalBaseChangeAlgebra K L i))ˣ)
    exact (localPointsEquiv K L n i).toEquiv.continuous_symm_iff.mpr
      ((localPointsEquiv K L n i).toMonoidHom.isOpenMap_of_sigmaCompact
        (localPointsEquiv K L n i).surjective (continuous_localPointsEquiv K L n i))

@[simp] theorem localPointsHomeomorph_toMulEquiv (n : ℕ) (i : Place K) :
    (localPointsHomeomorph K L n i).toMulEquiv = localPointsEquiv K L n i :=
  rfl

/-- The local points `GL_n(K_i)` of the group scheme `GL_n` over `K`. -/
def localGLEquiv (n : ℕ) (i : Place K) :
    PlaceGroupPoints K GLₙ i ≃* GL (Fin n) (placeCompletion K i) :=
  GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K) (placeCompletion K i)

/-- The local points `GL_n(K_i)` with their topology: the Library's homeomorphism for the
points of `GL_n`. -/
def localGLHomeomorph (n : ℕ) (i : Place K) :
    PlaceGroupPoints K GLₙ i ≃ₜ* GL (Fin n) (placeCompletion K i) :=
  GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
    (placeCompletion K i)

omit [FiniteDimensional K L] in
@[simp] theorem localGLHomeomorph_toMulEquiv (n : ℕ) (i : Place K) :
    (localGLHomeomorph K n i).toMulEquiv = localGLEquiv K n i :=
  rfl

omit [FiniteDimensional K L] in
/-- The exchange of factors carries `σ ⊗ 1` on `L ⊗_K K_i` to `σ_i = 1 ⊗ σ` on `E_i`. -/
theorem localSwap_coefficientConjugate (σ : L ≃ₐ[K] L) (i : Place K)
    (z : L ⊗[K] placeCompletion K i) :
    localSwap K L i (TensorGaloisPoint.coefficientConjugate K L (placeCompletion K i) σ z) =
      localGalois K L σ i (localSwap K L i z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change Algebra.TensorProduct.comm K L (placeCompletion K i) (σ a ⊗ₜ[K] b) =
      localGalois K L σ i (Algebra.TensorProduct.comm K L (placeCompletion K i) (a ⊗ₜ[K] b))
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [FiniteDimensional K L] in
/-- The exchange of factors carries `1 ⊗ x` in `L ⊗_K K_i` to `x ⊗ 1 = algebraMap x` in
`E_i`. -/
theorem localSwap_one_tmul (i : Place K) (x : placeCompletion K i) :
    localSwap K L i (1 ⊗ₜ[K] x) =
      algebraMap (placeCompletion K i) (LocalBaseChangeAlgebra K L i) x := by
  change Algebra.TensorProduct.comm K L (placeCompletion K i) (1 ⊗ₜ[K] x) = x ⊗ₜ[K] 1
  rw [Algebra.TensorProduct.comm_tmul]

/-- The Galois twist of `W = Res_{L/K} GL_n` acts on `W(K_i) = GL_n(E_i)` entrywise by
`σ_i = 1 ⊗ σ`. -/
theorem localPointsEquiv_twist (σ : L ≃ₐ[K] L) (n : ℕ) (i : Place K)
    (q : PlaceGroupPoints K Wₙ i) :
    localPointsEquiv K L n i
        (Langlands.GroupScheme.affinePointsTarget Wₙ (unitGaloisAut K L GLₙ σ).hom
          (placeCompletion K i) q) =
      entrywiseAut (localGalois K L σ i) n (localPointsEquiv K L n i q) := by
  change localPointsEquiv K L n i (Langlands.GroupScheme.affinePointsTarget Wₙ
      (AffineWeil.unitGaloisAction K L GLₙ σ) (placeCompletion K i) q) = _
  simp only [localPointsEquiv, MulEquiv.trans_apply]
  rw [AffineWeil.unitGaloisAction_groundPoints]
  change Units.mapEquiv (localSwap K L i).mapMatrix.toMulEquiv
      (GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K) _
        ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom
          (TensorGaloisPoint.coefficientConjugate K L (placeCompletion K i) σ)).op ≫ _)) = _
  rw [GroupScheme.GeneralLinear.affinePointsEquiv_naturality]
  ext a b
  simp only [Units.coe_mapEquiv, entrywiseAut_apply_apply]
  simp
  exact localSwap_coefficientConjugate K L σ i _

/-- The unit `GL_n → Res_{L/K} GL_n` is the base change `GL_n(K_i) → GL_n(E_i)` on local
points. -/
theorem localPointsEquiv_unit (n : ℕ) (i : Place K) (p : PlaceGroupPoints K GLₙ i) :
    localPointsEquiv K L n i
        (Langlands.GroupScheme.affinePointsTarget GLₙ (AffineWeil.unit K L GLₙ)
          (placeCompletion K i) p) =
      baseChange (placeCompletion K i) (LocalBaseChangeAlgebra K L i) n
        (localGLEquiv K n i p) := by
  simp only [localPointsEquiv, MulEquiv.trans_apply]
  rw [AffineWeil.unitGroundPointsEquiv_unit]
  change Units.mapEquiv (localSwap K L i).mapMatrix.toMulEquiv
      (GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K) _
        ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom
          (Algebra.TensorProduct.includeRight :
            placeCompletion K i →ₐ[K] L ⊗[K] placeCompletion K i)).op ≫ _)) = _
  rw [GroupScheme.GeneralLinear.affinePointsEquiv_naturality]
  ext a b
  simp only [Units.coe_mapEquiv, baseChange_apply_apply, localGLEquiv]
  simp
  exact localSwap_one_tmul K L i _

/-- The local component at `i` of the adelic twist `θ` is the entrywise action of `σ_i`. -/
theorem localPointsEquiv_atPlace_adelicAut (σ : L ≃ₐ[K] L) (n : ℕ) (i : Place K)
    (x : AdelicGroupPoints K Wₙ) :
    localPointsEquiv K L n i
        (AdelicGroupPoints.atPlace K Wₙ i (adelicAut K (unitGaloisAut K L GLₙ σ) x)) =
      entrywiseAut (localGalois K L σ i) n
        (localPointsEquiv K L n i (AdelicGroupPoints.atPlace K Wₙ i x)) := by
  rw [adelicAut_apply, AdelicGroupPoints.atPlace_map, localPointsEquiv_twist]

/-- The local component at `i` of the adelic norm `N(x) = x θ(x) ⋯ θ^{l-1}(x)` is the cyclic
norm `cyclicNorm σ_i l` of `GL_n(E_i)`. -/
theorem localPointsEquiv_atPlace_norm (σ : L ≃ₐ[K] L) (l n : ℕ) (i : Place K)
    (x : AdelicGroupPoints K Wₙ) :
    localPointsEquiv K L n i (AdelicGroupPoints.atPlace K Wₙ i
        ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x).prod) =
      cyclicNorm (localGalois K L σ i) l
        (localPointsEquiv K L n i (AdelicGroupPoints.atPlace K Wₙ i x)) := by
  rw [cyclicNorm, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  rw [← unitGaloisAutHom_apply, ← map_pow, unitGaloisAutHom_apply,
    localPointsEquiv_atPlace_adelicAut, localGalois_pow]

/-- The local component at `i` of the adelic unit `GL_n(𝔸_K) → W(𝔸_K)` is the base change
`GL_n(K_i) → GL_n(E_i)`. -/
theorem localPointsEquiv_atPlace_unit (n : ℕ) (i : Place K) (x : AdelicGroupPoints K GLₙ) :
    localPointsEquiv K L n i
        (AdelicGroupPoints.atPlace K Wₙ i
          (AdelicGroupPoints.map K GLₙ Wₙ (AffineWeil.unit K L GLₙ) x)) =
      baseChange (placeCompletion K i) (LocalBaseChangeAlgebra K L i) n
        (localGLEquiv K n i (AdelicGroupPoints.atPlace K GLₙ i x)) := by
  rw [AdelicGroupPoints.atPlace_map, localPointsEquiv_unit]

omit [FiniteDimensional K L] in
/-- `σ ↦ σ_i` is injective. -/
theorem localGaloisHom_injective (i : Place K) : Function.Injective (localGaloisHom K L i) := by
  intro σ τ h
  ext y
  have hy := congrArg (fun ρ : LocalBaseChangeAlgebra K L i ≃ₐ[placeCompletion K i]
    LocalBaseChangeAlgebra K L i => ρ ((1 : placeCompletion K i) ⊗ₜ[K] y)) h
  simp only [localGaloisHom_apply, localGalois_tmul] at hy
  let := placeCompletionField K i
  exact Algebra.TensorProduct.includeRight_injective (A := placeCompletion K i)
    (algebraMap K (placeCompletion K i)).injective hy

section CyclicAlgebra

open scoped PlaceCompletion

/-- If `σ` generates the Galois group of a cyclic extension `L/K` of degree `l`, then
`σ_i = id ⊗ σ` makes `E_i = K_i ⊗_K L` a cyclic `K_i`-algebra of degree `l`. -/
theorem isCyclicAlgebra_localGalois (σ : L ≃ₐ[K] L) (l : ℕ) (i : Place K)
    (h : IsCyclicAlgebra σ l) : IsCyclicAlgebra (localGalois K L σ i) l := by
  obtain ⟨-, hrank, -, hord, hfix⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · change Module.finrank (placeCompletion K i) (placeCompletion K i ⊗[K] L) = l
    rw [Module.finrank_baseChange, hrank]
  · change IsReduced (placeCompletion K i ⊗[K] L)
    have : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
    exact Algebra.FormallyUnramified.isReduced_of_field (placeCompletion K i) _
  · rw [← hord, ← localGaloisHom_apply]
    exact orderOf_injective _ (localGaloisHom_injective K L i) σ
  · intro x hx
    let f : K →ₗ[K] L := Algebra.linearMap K L
    let g : L →ₗ[K] L := σ.toLinearMap - LinearMap.id
    have hexact : Function.Exact f g := by
      intro y
      constructor
      · intro hy
        have : σ y = y := sub_eq_zero.mp hy
        obtain ⟨c, rfl⟩ := hfix y this
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        change σ (algebraMap K L c) - algebraMap K L c = 0
        rw [AlgEquiv.commutes, sub_self]
    have hexact' := Module.Flat.lTensor_exact (placeCompletion K i) hexact
    have hσ : ∀ z : placeCompletion K i ⊗[K] L,
        σ.toLinearMap.lTensor (placeCompletion K i) z =
          (localGalois K L σ i z : placeCompletion K i ⊗[K] L) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add z w hz hw =>
        rw [map_add, hz, hw]
        exact (map_add (localGalois K L σ i) z w).symm
    have hlin : ∀ z : placeCompletion K i ⊗[K] L, g.lTensor (placeCompletion K i) z =
        σ.toLinearMap.lTensor (placeCompletion K i) z - z := by
      intro z
      rw [LinearMap.lTensor_sub, LinearMap.lTensor_id, LinearMap.sub_apply, LinearMap.id_apply]
    have hkey : ∀ y : placeCompletion K i ⊗[K] K, f.lTensor (placeCompletion K i) y =
        (algebraMap (placeCompletion K i) (LocalBaseChangeAlgebra K L i)
          (TensorProduct.rid K (placeCompletion K i) y) : placeCompletion K i ⊗[K] L) := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul a b =>
        rw [TensorProduct.rid_tmul, LinearMap.lTensor_tmul]
        change a ⊗ₜ[K] algebraMap K L b = (b • a) ⊗ₜ[K] (1 : L)
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      | add z w hz hw => rw [map_add, hz, hw, map_add, map_add]; exact rfl
    have hg : g.lTensor (placeCompletion K i) x = 0 :=
      (hlin x).trans (sub_eq_zero.mpr ((hσ x).trans hx))
    obtain ⟨y, hy⟩ := (hexact' x).mp hg
    exact ⟨_, (hkey y).symm.trans hy⟩

end CyclicAlgebra

section Integral

/-- The integers `O_{E_v}` of `E_v = K_v ⊗_K L` at a finite place `v` of `K`: the subring
generated by `O_v ⊗ 1` and `1 ⊗ 𝓞_L`. -/
def localIntegers (v : Langlands.Global.FinitePlace K) : Subring (LocalBaseChangeAlgebra K L (.inr v)) :=
  Subring.closure
    ((Set.range fun x : v.adicCompletionIntegers K =>
        algebraMap (placeCompletion K (.inr v)) (LocalBaseChangeAlgebra K L (.inr v))
          (show placeCompletion K (.inr v) from (x : v.adicCompletion K))) ∪
      Set.range fun y : 𝓞 L =>
        (show LocalBaseChangeAlgebra K L (.inr v) from
          (1 : placeCompletion K (.inr v)) ⊗ₜ[K] (y : L)))

private theorem isOpen_isCompact_localIntegers (v : Langlands.Global.FinitePlace K) :
    IsOpen (localIntegers K L v : Set (LocalBaseChangeAlgebra K L (.inr v))) ∧
    IsCompact (localIntegers K L v : Set (LocalBaseChangeAlgebra K L (.inr v))) := by
  let : NumberField L := NumberField.of_module_finite K L
  let R := placeCompletion K (.inr v)
  let E := LocalBaseChangeAlgebra K L (.inr v)
  let O : Subring R := (v.adicCompletionIntegers K).toSubring
  let : Algebra O E := Algebra.compHom E O.subtype
  let g : 𝓞 L →ₐ[ℤ] E :=
    ((Algebra.TensorProduct.includeRight (R := K) (A := R) (B := L)).toRingHom.comp
      (algebraMap (𝓞 L) L)).toIntAlgHom
  let b := RingOfIntegers.basis L
  let a : Module.Free.ChooseBasisIndex ℤ (𝓞 L) → E := fun j => g (b j)
  let f := Fintype.linearCombination R a
  let fO := Fintype.linearCombination O a
  -- The image of the integral basis spans the generated subring over O.
  have hspan : g.range.toSubmodule = Submodule.span ℤ (Set.range a) := by
    calc
      g.range.toSubmodule = (⊤ : Submodule ℤ (𝓞 L)).map g.toLinearMap := by
        rw [Submodule.map_top]
        rfl
      _ = _ := by
        rw [← b.span_eq, Submodule.map_span, ← Set.range_comp]
        rfl
  have hadjoin : (Algebra.adjoin O (g.range : Set E)).toSubring = localIntegers K L v := by
    rw [Algebra.adjoin_eq_ring_closure]
    rfl
  have hrange : (localIntegers K L v : Set E) = (LinearMap.range fO : Set E) := by
    rw [Fintype.range_linearCombination, ← g.range.adjoin_eq_span_of_eq_span O hspan]
    exact congrArg (fun S : Subring E => (S : Set E)) hadjoin.symm
  have himage : (localIntegers K L v : Set E) =
      f '' Set.pi Set.univ (fun _ => (O : Set R)) := by
    rw [hrange]
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun j => (c j : R), fun j _ => (c j).property, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨fun j => ⟨c j, hc j (Set.mem_univ _)⟩, rfl⟩
  -- Over the completed field, the same family spans the entire local algebra.
  have hf : Function.Surjective f := by
    apply (span_range_eq_top_iff_surjective_fintypeLinearCombination R a).mp
    have hL : Submodule.span K (Set.range (integralBasis L)) = ⊤ :=
      Submodule.span_eq_top_of_span_eq_top ℚ K _ (integralBasis L).span_eq
    have ha : Set.range a = TensorProduct.mk K R L 1 '' Set.range (integralBasis L) := by
      rw [← Set.range_comp]
      congr 1
      funext j
      exact congrArg (fun y : L => (1 : R) ⊗ₜ[K] y) (integralBasis_apply L j).symm
    have hbase := congrArg (Submodule.baseChange R) hL
    rw [Submodule.baseChange_span, Submodule.baseChange_top] at hbase
    rw [ha]
    exact hbase
  rw [himage]
  refine ⟨IsModuleTopology.isOpenMap_of_surjective hf _ ?_, ?_⟩
  · exact isOpen_set_pi Set.finite_univ fun _ _ =>
      (show IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) from
        Valued.isOpen_valuationSubring _)
  · exact (isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers K v).image
      (IsModuleTopology.continuous_of_linearMap f)

/-- The subring `O_{E_v}` is open in `E_v`. -/
theorem isOpen_localIntegers (v : Langlands.Global.FinitePlace K) :
    IsOpen (localIntegers K L v : Set (LocalBaseChangeAlgebra K L (.inr v))) :=
  (isOpen_isCompact_localIntegers K L v).1

/-- The subring `O_{E_v}` is compact in `E_v`. -/
theorem isCompact_localIntegers (v : Langlands.Global.FinitePlace K) :
    IsCompact (localIntegers K L v : Set (LocalBaseChangeAlgebra K L (.inr v))) :=
  (isOpen_isCompact_localIntegers K L v).2

/-- The subgroup `GL_n(O_{E_v})` of `W(K_v) = GL_n(E_v)` at a finite place `v` of `K`. -/
def localIntegralSubgroup (n : ℕ) (v : Langlands.Global.FinitePlace K) :
    Subgroup (PlaceGroupPoints K Wₙ (.inr v)) :=
  (Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v)).comap
    (localPointsEquiv K L n (.inr v)).toMonoidHom

/-- The subgroup `GL_n(O_{E_v})` is open in `W(K_v)`. -/
theorem isOpen_localIntegralSubgroup (n : ℕ) (v : Langlands.Global.FinitePlace K) :
    IsOpen (localIntegralSubgroup K L n v : Set (PlaceGroupPoints K Wₙ (.inr v))) :=
  (Langlands.GeneralLinearGroup.isOpen_integralSubgroup (Fin n) (localIntegers K L v)
      (isOpen_localIntegers K L v)).preimage
    (localPointsHomeomorph K L n (.inr v)).continuous

/-- The subgroup `GL_n(O_{E_v})` is compact in `W(K_v)`. -/
theorem isCompact_localIntegralSubgroup (n : ℕ) (v : Langlands.Global.FinitePlace K) :
    IsCompact (localIntegralSubgroup K L n v : Set (PlaceGroupPoints K Wₙ (.inr v))) :=
  (localPointsHomeomorph K L n (.inr v)).toHomeomorph.isCompact_preimage.mpr
    (Langlands.GeneralLinearGroup.isCompact_integralSubgroup (Fin n) (localIntegers K L v)
      (isCompact_localIntegers K L v))

/-- The subgroups of `W(K_i)` given by `GL_n(O_{E_v})` at finite places `v` and by the
whole group at infinite places. -/
def localIntegralFamily (n : ℕ) : (i : Place K) → Subgroup (PlaceGroupPoints K Wₙ i)
  | .inl _ => ⊤
  | .inr v => localIntegralSubgroup K L n v

omit [FiniteDimensional K L] in
/-- `σ_v = id ⊗ σ` preserves the integers `O_{E_v}`. -/
theorem localGalois_mem_localIntegers (σ : L ≃ₐ[K] L) (v : Langlands.Global.FinitePlace K)
    {x : LocalBaseChangeAlgebra K L (.inr v)} (hx : x ∈ localIntegers K L v) :
    localGalois K L σ (.inr v) x ∈ localIntegers K L v := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
    apply Subring.subset_closure
    rcases hy with ⟨c, rfl⟩ | ⟨y, rfl⟩
    · left
      exact ⟨c, (AlgEquiv.commutes _ _).symm⟩
    · right
      refine ⟨⟨σ y, ?_⟩, ?_⟩
      · exact (y.2.map (σ : L →+* L).toIntAlgHom)
      · change (1 : placeCompletion K (.inr v)) ⊗ₜ[K] σ (y : L) =
          localGalois K L σ (.inr v) ((1 : placeCompletion K (.inr v)) ⊗ₜ[K] (y : L))
        rw [localGalois_tmul]
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- The twist `θ` preserves each subgroup in `localIntegralFamily`. -/
theorem twist_mem_localIntegralFamily (σ : L ≃ₐ[K] L) (n : ℕ) (i : Place K)
    (q : PlaceGroupPoints K Wₙ i) (hq : q ∈ localIntegralFamily K L n i) :
    Langlands.GroupScheme.affinePointsTarget Wₙ (unitGaloisAut K L GLₙ σ).hom
        (placeCompletion K i) q ∈ localIntegralFamily K L n i := by
  cases i with
  | inl w => exact Subgroup.mem_top _
  | inr v =>
    change localPointsEquiv K L n (.inr v) q ∈
      Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v) at hq
    change localPointsEquiv K L n (.inr v) _ ∈
      Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v)
    rw [localPointsEquiv_twist]
    rw [Langlands.GeneralLinearGroup.mem_integralSubgroup] at hq ⊢
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [entrywiseAut_apply_apply]
      exact localGalois_mem_localIntegers K L σ v (hq.1 a b)
    · rw [← map_inv, entrywiseAut_apply_apply]
      exact localGalois_mem_localIntegers K L σ v (hq.2 a b)

end Integral

/-- The subgroup `GL_n(O_v)` of `GL_n(K_v)` at a finite place `v` of `K`. -/
def glIntegralSubgroup (n : ℕ) (v : Langlands.Global.FinitePlace K) :
    Subgroup (PlaceGroupPoints K GLₙ (.inr v)) :=
  (Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
      (show Subring (placeCompletion K (.inr v)) from
        (v.adicCompletionIntegers K).toSubring)).comap
    (localGLEquiv K n (.inr v)).toMonoidHom

/-- `GL_n(O_v)` is open in `GL_n(K_v)`. -/
theorem isOpen_glIntegralSubgroup (n : ℕ) (v : Langlands.Global.FinitePlace K) :
    IsOpen (glIntegralSubgroup K n v : Set (PlaceGroupPoints K GLₙ (.inr v))) :=
  (Langlands.GeneralLinearGroup.isOpen_integralSubgroup (Fin n)
      (show Subring (placeCompletion K (.inr v)) from (v.adicCompletionIntegers K).toSubring)
      (show IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) from
        Valued.isOpen_valuationSubring _)).preimage
    (localGLHomeomorph K n (.inr v)).continuous

/-- `GL_n(O_v)` is compact. -/
theorem isCompact_glIntegralSubgroup (n : ℕ) (v : Langlands.Global.FinitePlace K) :
    IsCompact (glIntegralSubgroup K n v : Set (PlaceGroupPoints K GLₙ (.inr v))) :=
  (localGLHomeomorph K n (.inr v)).toHomeomorph.isCompact_preimage.mpr
    (Langlands.GeneralLinearGroup.isCompact_integralSubgroup (Fin n)
      (show Subring (placeCompletion K (.inr v)) from (v.adicCompletionIntegers K).toSubring)
      (Langlands.Global.isCompact_adicCompletionIntegers K v))

/-- The family of subgroups `GL_n(O_v)` at the finite places of `K`, and the whole group at
the infinite places. -/
def glIntegralFamily (n : ℕ) : (i : Place K) → Subgroup (PlaceGroupPoints K GLₙ i)
  | .inl _ => ⊤
  | .inr v => glIntegralSubgroup K n v

private theorem mem_standardSubgroup (n : ℕ) (v : Langlands.Global.FinitePlace K)
    (p : (GLₙ).affinePoints (CommAlgCat.of K (FiniteCompletion K v)))
    (hp : p ∈ glIntegralSubgroup K n v) :
    p ∈ LinearIntegralFamily.subgroup K GLₙ
      (MatrixRepresentation.standard (Fin n) (CommRingCat.of K)) v := by
  let S := CommAlgCat.of K (FiniteCompletion K v)
  change (MatrixRepresentation.standard (Fin n) (CommRingCat.of K)).affineMatrix S p ∈
    Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (v.adicCompletionIntegers K).toSubring
  rw [MatrixRepresentation.standard_affineMatrix (n := Fin n) (R := CommRingCat.of K) S p]
  exact hp

/-- Each regular function is integral on the entire subgroup `GL_n(O_v)` at almost all
finite places. -/
theorem isUniformlyIntegral_glIntegralFamily (n : ℕ) :
    AdelicGroupPoints.IsUniformlyIntegral K GLₙ (glIntegralFamily K n) := by
  intro a
  let ρ := MatrixRepresentation.standard (Fin n) (CommRingCat.of K)
  have hρ : IsClosedSubgroup ρ := by
    change IsClosedImmersion (𝟙 _)
    infer_instance
  exact (LinearIntegralFamily.eventually_uniform_integral K GLₙ ρ hρ a).mono
    (fun v hv p hp => hv p (mem_standardSubgroup K n v p hp))

/-- The unit `GL_n → Res_{L/K} GL_n` on local points: `GL_n(K_i) → W(K_i)`. -/
def localUnitHom (n : ℕ) (i : Place K) : PlaceGroupPoints K GLₙ i →* PlaceGroupPoints K Wₙ i :=
  Langlands.GroupScheme.affinePointsTarget GLₙ (AffineWeil.unit K L GLₙ) (placeCompletion K i)

theorem localPointsEquiv_localUnitHom (n : ℕ) (i : Place K) (p : PlaceGroupPoints K GLₙ i) :
    localPointsEquiv K L n i (localUnitHom K L n i p) =
      baseChange (placeCompletion K i) (LocalBaseChangeAlgebra K L i) n
        (localGLEquiv K n i p) :=
  localPointsEquiv_unit K L n i p

/-- The unit `GL_n → Res_{L/K} GL_n` maps each subgroup in `glIntegralFamily` into its
counterpart in `localIntegralFamily`. -/
theorem localUnitHom_mem_localIntegralFamily (n : ℕ) (i : Place K)
    (p : PlaceGroupPoints K GLₙ i) (hp : p ∈ glIntegralFamily K n i) :
    localUnitHom K L n i p ∈ localIntegralFamily K L n i := by
  cases i with
  | inl w => exact Subgroup.mem_top _
  | inr v =>
    change localGLEquiv K n (.inr v) p ∈ Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
      (show Subring (placeCompletion K (.inr v)) from (v.adicCompletionIntegers K).toSubring)
      at hp
    change localPointsEquiv K L n (.inr v) _ ∈
      Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v)
    rw [localPointsEquiv_localUnitHom]
    rw [Langlands.GeneralLinearGroup.mem_integralSubgroup] at hp ⊢
    have hgen : ∀ c : placeCompletion K (.inr v),
        c ∈ (show Subring (placeCompletion K (.inr v)) from
          (v.adicCompletionIntegers K).toSubring) →
        algebraMap (placeCompletion K (.inr v)) (LocalBaseChangeAlgebra K L (.inr v)) c ∈
          localIntegers K L v := fun c hc =>
      Subring.subset_closure (Or.inl ⟨⟨c, hc⟩, rfl⟩)
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [baseChange_apply_apply]
      exact hgen _ (hp.1 a b)
    · rw [← map_inv, baseChange_apply_apply]
      exact hgen _ (hp.2 a b)

/-- A function `φ` on `G(𝔸_K)` is the restricted tensor product of local functions `φ_i` at
the places `i ∈ T` and of the indicator functions of the subgroups `U_i` at the places
`i ∉ T`: `φ(x) = ∏_{i ∈ T} φ_i(x_i)` if `x_i ∈ U_i` for all `i ∉ T`, and `φ(x) = 0`
otherwise. -/
def IsAdelicFactorization {G : GroupScheme (Spec (CommRingCat.of K))} (T : Finset (Place K))
    (φloc : (i : Place K) → PlaceGroupPoints K G i → ℂ)
    (U : (i : Place K) → Subgroup (PlaceGroupPoints K G i))
    (φ : AdelicGroupPoints K G → ℂ) : Prop :=
  ∀ x : AdelicGroupPoints K G,
    φ x = {y : AdelicGroupPoints K G | ∀ i ∉ T, AdelicGroupPoints.atPlace K G i y ∈ U i}.indicator
      (fun y => ∏ i ∈ T, φloc i (AdelicGroupPoints.atPlace K G i y)) x

end Langlands.TraceFormula
