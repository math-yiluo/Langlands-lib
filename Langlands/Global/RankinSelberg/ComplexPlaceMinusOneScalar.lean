import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.FiniteVectors
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof

/-! # The scalar of `-1` at a complex place of an actual cuspidal realization

Let `T` be an actual cuspidal realization of `GL_(r+1)` over a number field `F` and `w` a
complex place of `F`. If `T` has the standard-module parameter of the list `ds` of complex
characters at `w` (`HasComplexPlaceParameter`), then `-1 ∈ U(r+1)` at `w` acts on `T` by the
scalar `∏_j χ_j(-1)`, so `complexMinusOneScalar T w = ∏_j χ_j(-1)`
(`complexMinusOneScalar_eq_prod`).

The proof:

* `-1` at `w` is a central element of the infinite adelic group, whose archimedean
  coordinate matrix is the scalar matrix of the element `(1, (-1 at w, 1 elsewhere))` of the
  mixed space; so it commutes with the standard infinite compact, with the finite adelic
  group, and its adjoint action on the complexified Lie algebra and on the enveloping algebra
  is trivial. Hence its compact operator commutes with every element of the concrete operator
  algebra, and every eigenspace of it in an operator realization is a subrepresentation.
* On the complex principal series of `ds`, right translation by `-1 = diag(-1, …, -1)`
  multiplies every function by `∏_j χ_j(-1)` (the modulus factor is `1`).
* The `U(r+1)`-finite functions of the principal series contain a nonzero function
  (`complexStandardNontrivial`); its image under the injective equivariant map of the
  parameter is a nonzero eigenvector of `-1` at `w` with eigenvalue `∏_j χ_j(-1)`. By
  irreducibility the eigenspace is everything.
-/

noncomputable section
universe u
open NumberField
open scoped Classical
open scoped Manifold ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexPlaceMinusOne

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance minusOneRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance minusOneContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance minusOneSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance minusOneFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance minusOneStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-! ### `-1` at a complex place is central -/

/-- The element of the mixed space `ℝ^(real places) × ℂ^(complex places)` equal to `-1` at
the complex place `w` and to `1` at every other place. -/
def minusOneMixed (w : CP) : mixedEmbedding.mixedSpace F :=
  (1, Pi.mulSingle w (-1 : ℂ))

omit [NumberField F] in
/-- The archimedean coordinate matrix of `-1` at `w` is the scalar matrix of
`minusOneMixed w`. -/
theorem coordinates_minusOne (w : CP) :
    ((archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n w (-1)).val :
        ArchimedeanGL F n) : ArchimedeanMatrix F n) =
      Matrix.scalar (Fin n) (minusOneMixed w) := by
  ext i j v
  · have h := congrFun (congrFun (realMatrix_complexPlaceCompactInclusion F n w v (-1)) i) j
    change ArchimedeanGL.realMatrix F n _ v i j = _
    rw [h]
    by_cases hij : i = j
    · subst hij
      simp [minusOneMixed]
    · simp [minusOneMixed, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
  · have h :=
      congrFun (congrFun (complexMatrix_complexPlaceCompactInclusion F n w v (-1)) i) j
    change ArchimedeanGL.complexMatrix F n _ v i j = _
    rw [h]
    by_cases hv : v = w
    · subst hv
      by_cases hij : i = j
      · subst hij
        simp [minusOneMixed, Unitary.coe_neg]
      · simp [minusOneMixed, Unitary.coe_neg, Matrix.one_apply_ne hij,
          Matrix.diagonal_apply_ne _ hij]
    · by_cases hij : i = j
      · subst hij
        simp [minusOneMixed, Pi.mulSingle_eq_of_ne hv]
      · simp [minusOneMixed, Pi.mulSingle_eq_of_ne hv, Matrix.one_apply_ne hij,
          Matrix.diagonal_apply_ne _ hij]

omit [NumberField F] in
/-- The coordinate matrix of `-1` at `w` commutes with every archimedean matrix. -/
theorem coordinates_minusOne_commute (w : CP) (X : ArchimedeanMatrix F n) :
    ((archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n w (-1)).val :
        ArchimedeanGL F n) : ArchimedeanMatrix F n) * X =
      X * ((archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n w (-1)).val :
        ArchimedeanGL F n) : ArchimedeanMatrix F n) := by
  rw [coordinates_minusOne]
  exact (Matrix.scalar_commute (minusOneMixed w) (fun r => Commute.all _ r) X).eq

omit [NumberField F] in
/-- `-1` at `w` is central in the infinite adelic group. -/
theorem minusOne_mul_comm (w : CP) (g : InfiniteAdelicGL F n) :
    (complexPlaceCompactInclusion F n w (-1)).val * g =
      g * (complexPlaceCompactInclusion F n w (-1)).val := by
  apply (archimedeanGLCoordinates F n).injective
  rw [map_mul, map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact coordinates_minusOne_commute w _

omit [NumberField F] in
/-- The adjoint action of `-1` at `w` on the real Lie algebra is trivial. -/
theorem realLieConjugation_minusOne (w : CP) (X : ArchimedeanGL.RealLieAlgebra F n) :
    ArchimedeanGL.realLieConjugation F n (complexPlaceCompactInclusion F n w (-1)).val X =
      X := by
  apply (ArchimedeanGL.realLieAlgebraToMatrix F n).injective
  rw [ArchimedeanGL.realLieAlgebraToMatrix_realLieConjugation, coordinates_minusOne_commute,
    mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, mul_one]

omit [NumberField F] in
/-- The adjoint action of `-1` at `w` on the complexified Lie algebra is trivial. -/
theorem complexLieConjugation_minusOne (w : CP) (X : ArchimedeanGL.ComplexLieAlgebra F n) :
    ArchimedeanGL.complexLieConjugation F n (complexPlaceCompactInclusion F n w (-1)).val X =
      X := by
  induction X using TensorProduct.inductionOn with
  | tmul c Y => rw [ArchimedeanGL.complexLieConjugation_tmul, realLieConjugation_minusOne]
  | add X Y hX hY => rw [map_add, hX, hY]

section Enveloping

attribute [local instance 100] LieRing.ofAssociativeRing

omit [NumberField F] in
/-- The adjoint action of `-1` at `w` on the enveloping algebra is trivial. -/
theorem envelopingConjugation_minusOne (w : CP) (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    ArchimedeanGL.envelopingConjugation F n (complexPlaceCompactInclusion F n w (-1)).val a =
      a := by
  have h : ((ArchimedeanGL.envelopingConjugation F n
      (complexPlaceCompactInclusion F n w (-1)).val : ArchimedeanGL.EnvelopingAlgebra F n ≃ₐ[ℂ]
        ArchimedeanGL.EnvelopingAlgebra F n) : ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ]
          ArchimedeanGL.EnvelopingAlgebra F n) = AlgHom.id ℂ _ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    change ArchimedeanGL.envelopingConjugation F n (complexPlaceCompactInclusion F n w (-1)).val
      (ArchimedeanGL.envelopingGenerator F n X) = ArchimedeanGL.envelopingGenerator F n X
    rw [ArchimedeanGL.envelopingConjugation_generator, complexLieConjugation_minusOne]
  exact AlgHom.congr_fun h a

end Enveloping

/-! ### The compact operator of `-1` at `w` is central in the operator algebra -/

/-- The compact operator of `-1` at `w` commutes with every element of the concrete operator
algebra. -/
theorem minusOne_commute_operator (w : CP) :
    ∀ b ∈ automorphicOperatorAlgebra F n,
      Commute (finiteSmoothCompactRightAction F n (complexPlaceCompactInclusion F n w (-1))) b := by
  intro b hb
  refine Algebra.adjoin_induction (p := fun b _ =>
    Commute (finiteSmoothCompactRightAction F n (complexPlaceCompactInclusion F n w (-1))) b)
    ?_ ?_ ?_ ?_ hb
  · rintro b ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨a, rfl⟩)
    · change finiteSmoothRightAction F n
          (AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n w (-1)).val) *
          finiteSmoothRightAction F n (AdelicGL.ofFinite F n d) =
        finiteSmoothRightAction F n (AdelicGL.ofFinite F n d) *
          finiteSmoothRightAction F n
            (AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n w (-1)).val)
      rw [← map_mul, ← map_mul,
        (AdelicGL.ofFinite_commute_ofInfinite F n d
          (complexPlaceCompactInclusion F n w (-1)).val).eq]
    · change finiteSmoothRightAction F n
          (AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n w (-1)).val) *
          finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) =
        finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) *
          finiteSmoothRightAction F n
            (AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n w (-1)).val)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, minusOne_mul_comm]
    · apply LinearMap.ext
      intro f
      change finiteSmoothRightAction F n
          (AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n w (-1)).val)
          (finiteSmoothEnvelopingAction F n a f) =
        finiteSmoothEnvelopingAction F n a
          (finiteSmoothRightAction F n
            (AdelicGL.ofInfinite F n (complexPlaceCompactInclusion F n w (-1)).val) f)
      rw [finiteSmoothRightAction_envelopingAction, envelopingConjugation_minusOne]
  · intro c
    exact Algebra.commute_algebraMap_right c _
  · intro x y _ _ hx hy
    exact hx.add_right hy
  · intro x y _ _ hx hy
    exact hx.mul_right hy

local instance minusOneSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- On an operator realization, `-1` at `w` commutes with the whole operator algebra. -/
theorem complexPlaceCompactRepresentation_minusOne_representation (S : OperatorRealization F n)
    (w : CP) (a : automorphicOperatorAlgebra F n) (x : S.Space) :
    S.complexPlaceCompactRepresentation w (-1) (S.representation a x) =
      S.representation a (S.complexPlaceCompactRepresentation w (-1) x) := by
  apply Subtype.ext
  apply Subtype.ext
  exact LinearMap.congr_fun (minusOne_commute_operator w a.val a.property).eq x.val.val

/-- The eigenspace of `-1` at `w` for the eigenvalue `c`, a subrepresentation. -/
def minusOneEigenspace (S : OperatorRealization F n) (w : CP) (c : ℂ) :
    Subrepresentation S.representation where
  toSubmodule := Module.End.eigenspace (S.complexPlaceCompactRepresentation w (-1)) c
  apply_mem_toSubmodule a x hx := by
    have hx' : S.complexPlaceCompactRepresentation w (-1) x = c • x :=
      Module.End.mem_eigenspace_iff.1 hx
    have key : S.complexPlaceCompactRepresentation w (-1) (S.representation a x) =
        c • S.representation a x :=
      (complexPlaceCompactRepresentation_minusOne_representation S w a x).trans
        ((congrArg (S.representation a) hx').trans (map_smul (S.representation a) c x))
    exact Module.End.mem_eigenspace_iff.2 key

theorem mem_minusOneEigenspace (S : OperatorRealization F n) (w : CP) (c : ℂ) (x : S.Space) :
    x ∈ (minusOneEigenspace S w c).toSubmodule ↔
      S.complexPlaceCompactRepresentation w (-1) x = c • x :=
  Module.End.mem_eigenspace_iff

/-! ### `-1` on the complex principal series -/

/-- `∏_(i < length ds)` of the position characters at `z` is the product of the characters of
`ds` at `z`. -/
theorem prod_complexPositionCharacter (ds : List ComplexCharacterData) (z : ℂˣ) :
    ∏ i : Fin ds.length, complexPositionCharacter ds i z =
      (ds.map fun d => ((d.character z : ℂˣ) : ℂ)).prod := by
  rw [Fin.prod_univ_eq_prod_range (fun i => complexPositionCharacter ds i z)]
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [List.length_cons, Finset.prod_range_succ', List.map_cons, List.prod_cons, ← ih,
      mul_comm]
    rfl

/-- The principal series character of `ds` at `diag(-1, …, -1)` is `∏_j χ_j(-1)`. -/
theorem principalSeriesCharacter_neg_one (N : ℕ) (ds : List ComplexCharacterData)
    (hN : ds.length = N) :
    principalSeriesCharacter ℂ N (complexPositionCharacter ds) (fun _ => -1) =
      (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod := by
  subst hN
  rw [← prod_complexPositionCharacter]
  unfold principalSeriesCharacter
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/-- Right translation by `-1` multiplies every function of the complex principal series of
`ds` by `∏_j χ_j(-1)`. -/
theorem rightTranslation_neg_one (N : ℕ) (ds : List ComplexCharacterData) (hN : ds.length = N)
    (f : Langlands.GeneralLinear N ℂ → ℂ) (hf : f ∈ complexStandardModule N ds) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℂ) (-1) f =
      (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod • f := by
  funext g
  have hdiag : (GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin N => (-1 : ℂˣ)) :
      Langlands.GeneralLinear N ℂ) = -1 := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [GeneralLinear.Iwasawa.diagonalUnits]
    · simp [GeneralLinear.Iwasawa.diagonalUnits, Matrix.diagonal_apply_ne _ hij,
        Matrix.one_apply_ne hij]
  have hg : g * -1 = (GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin N => (-1 : ℂˣ)) :
      Langlands.GeneralLinear N ℂ) *
        ((1 : GeneralLinear.upperUnipotent N ℂ) : Langlands.GeneralLinear N ℂ) * g := by
    rw [hdiag]
    simp
  change f (g * -1) = (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod * f g
  rw [hg, hf.2, principalSeriesCharacter_neg_one N ds hN]

/-! ### The scalar -/

/-- `-1` as an element of `U(N)`. -/
def negOneUnitary (N : ℕ) : unitaryCompact ℂ N :=
  ⟨-1, by
    change ((-1 : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ) ∈
      Matrix.unitaryGroup (Fin N) ℂ
    rw [Units.val_neg, Units.val_one]
    exact (-1 : Matrix.unitaryGroup (Fin N) ℂ).2⟩

/-- The unitary matrix underlying `negOneUnitary N` is `-1`. -/
theorem negOneUnitary_unitaryGroup (N : ℕ) :
    (⟨((negOneUnitary N : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ),
      (negOneUnitary N).2⟩ : Matrix.unitaryGroup (Fin N) ℂ) = -1 := by
  apply Subtype.ext
  change ((-1 : Langlands.GeneralLinear N ℂ) : Matrix (Fin N) (Fin N) ℂ) =
    ((-1 : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  rw [Units.val_neg, Units.val_one, Unitary.coe_neg, OneMemClass.coe_one]

/-- The compact action of the unitary matrix underlying `negOneUnitary n` is that of `-1`. -/
theorem complexPlaceCompactRepresentation_negOneUnitary (S : OperatorRealization F n) (w : CP)
    (x : S.Space) :
    S.complexPlaceCompactRepresentation w
        ⟨((negOneUnitary n : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ),
          (negOneUnitary n).2⟩ x =
      S.complexPlaceCompactRepresentation w (-1) x :=
  congrArg (fun k => S.complexPlaceCompactRepresentation w k x) (negOneUnitary_unitaryGroup n)

/-- Right translation by `negOneUnitary N` on the `U(N)`-finite functions of the complex
standard module of `ds` is multiplication by `∏_j χ_j(-1)`. -/
theorem negOneUnitary_translate (N : ℕ) (ds : List ComplexCharacterData) (hN : ds.length = N)
    (f : complexStandardKFinite N ds)
    (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℂ)
      (negOneUnitary N : Langlands.GeneralLinear N ℂ) (f : Langlands.GeneralLinear N ℂ → ℂ) ∈
        complexStandardKFinite N ds) :
    (⟨_, hf⟩ : complexStandardKFinite N ds) =
      (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod • f := by
  apply Subtype.ext
  exact rightTranslation_neg_one N ds hN f.val (Submodule.mem_inf.mp f.2).1

variable [CompactSpace (AdeleQuotient F)]

/-- If the actual cuspidal realization `T` has the parameter `ds` at the complex place `w`,
then `-1` at `w` has a nonzero eigenvector in `T` with eigenvalue `∏_j χ_j(-1)`. -/
theorem exists_minusOne_eigenvector {r : ℕ} (T : CuspidalOperatorRealization F r) (w : CP)
    (ds : List ComplexCharacterData) (hd : T.realization.HasComplexPlaceParameter w ds) :
    ∃ y : T.realization.Space, y ≠ 0 ∧
      T.realization.complexPlaceCompactRepresentation w (-1) y =
        (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod • y := by
  obtain ⟨hlen, A, hA, hK, -⟩ := hd
  have : Nontrivial (complexStandardKFinite (r + 1) ds) :=
    complexStandardNontrivial (r + 1) ds hlen
  have hne := exists_ne (0 : complexStandardKFinite (r + 1) ds)
  obtain ⟨f, hf0⟩ := hne
  have hAf0 : A f ≠ 0 := fun h => hf0 (hA (h.trans (map_zero A).symm))
  have hK' := hK (negOneUnitary (r + 1)) f
  obtain ⟨hf, hAf⟩ := hK'
  have h1 := complexPlaceCompactRepresentation_negOneUnitary T.realization w (A f)
  have h2 := negOneUnitary_translate (r + 1) ds hlen f hf
  have h3 : A ⟨_, hf⟩ = (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod • A f :=
    (congrArg A h2).trans (map_smul A _ f)
  exact ⟨A f, hAf0, h1.symm.trans (hAf.symm.trans h3)⟩

/-- In an irreducible realization, a nonzero eigenvector of `-1` at `w` with eigenvalue `c`
forces `-1` at `w` to act by `c` everywhere. -/
theorem minusOne_eq_smul_of_eigenvector {r : ℕ} (T : CuspidalOperatorRealization F r) (w : CP)
    (c : ℂ) (y : T.Space) (hy0 : y ≠ 0)
    (hy : T.realization.complexPlaceCompactRepresentation w (-1) y = c • y) (x : T.Space) :
    T.realization.complexPlaceCompactRepresentation w (-1) x = c • x := by
  have h1 := T.irreducible.eq_bot_or_eq_top (minusOneEigenspace T.realization w c)
  rcases h1 with h | h
  · exfalso
    apply hy0
    have hmem : y ∈ (minusOneEigenspace T.realization w c).toSubmodule :=
      (mem_minusOneEigenspace T.realization w c y).2 hy
    rw [h] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · have hx : x ∈ (minusOneEigenspace T.realization w c).toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    exact (mem_minusOneEigenspace T.realization w c x).1 hx

/-- **`complexMinusOneScalar` at a complex place with a parameter.** If the actual cuspidal
realization `T` of `GL_(r+1)` has the parameter `ds` at the complex place `w`, then `-1` at `w`
acts on `T` by `∏_j χ_j(-1)`, so `complexMinusOneScalar T w = ∏_j χ_j(-1)`. -/
theorem complexMinusOneScalar_eq_prod {r : ℕ} (T : CuspidalOperatorRealization F r) (w : CP)
    (ds : List ComplexCharacterData) (hd : T.realization.HasComplexPlaceParameter w ds) :
    complexMinusOneScalar T w = (ds.map fun d => ((d.character (-1) : ℂˣ) : ℂ)).prod := by
  obtain ⟨y, hy0, hy⟩ := exists_minusOne_eigenvector T w ds hd
  have hall := minusOne_eq_smul_of_eigenvector T w _ y hy0 hy
  have hspec := complexMinusOneScalar_spec T w ⟨_, hall⟩ y
  rw [hall] at hspec
  exact (smul_left_injective ℂ hy0 hspec).symm

end Langlands.Global.RankinSelbergGlobal.ComplexPlaceMinusOne
