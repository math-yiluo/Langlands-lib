import Langlands.GroupScheme.Derived.CentralIntersection.BlockCharacter
import Langlands.GroupScheme.Derived.CentralIntersection.PointVanishing

/-! # A unipotence criterion over an algebraically closed field

Let `H` be a reduced connected affine group scheme, locally of finite type over an algebraically
closed field `K`, whose rational points commute, with a closed embedding `ρ : H ⟶ GL_N` such
that every eigenvalue of every rational point is an `m`-th root of unity for a fixed `m ≠ 0`.
Then `H` is unipotent.

The proof first shows that the universal matrix `M = ρ(id)` satisfies `(M - 1)^e = 0` over
`Γ(H, 𝒪)`: `M` is annihilated by `Q = (X^m - 1)^(N+1)` (pointwise, then by reducedness), and the
idempotent `E` splitting off the eigenvalue `1` has determinant `0` or `1` by connectedness, and
`1` at the identity point. Right translation by a rational point then acts locally unipotently
on the entries of `M` and `M⁻¹`, which generate `Γ(H, 𝒪)`; hence every rational point acts
unipotently in every representation, and commuting unipotent matrices have a common fixed
vector, which is fixed scheme-theoretically by reducedness. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.CentralIntersection

section Evaluation

variable {K : Type u} [Field K] {H : GroupScheme (Spec (CommRingCat.of K))}

/-- Evaluation of global functions of `H` at a rational point. -/
def evalPoint (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) : Γ(H.X.left, ⊤) →+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp h.left.appTop.hom

theorem evalPoint_apply (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)
    (f : Γ(H.X.left, ⊤)) :
    evalPoint h f = (Scheme.ΓSpecIso (CommRingCat.of K)).hom (h.left.appTop f) :=
  rfl

/-- Evaluation at a rational point is the identity on scalars. -/
theorem evalPoint_scalarMap (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) (c : K) :
    evalPoint h (scalarMap H.X c) = c := by
  rw [evalPoint_apply, scalarMap_naturality]
  exact scalarMap_base (R := CommRingCat.of K) c

variable {n : Type} [Fintype n] [DecidableEq n]

theorem evalPoint_mapMatrix_scalarMap (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)
    (A : Matrix n n K) : (evalPoint h).mapMatrix ((scalarMap H.X).mapMatrix A) = A := by
  ext i j
  exact evalPoint_scalarMap h (A i j)

/-- Evaluating the universal matrix of a representation at a rational point gives the matrix of
that point. -/
theorem evalPoint_mapMatrix_pointMatrix (σ : MatrixRepresentation H n)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :
    (σ.pointMatrix H.X (𝟙 H.X) : Matrix n n Γ(H.X.left, ⊤)).map (evalPoint h) =
      (σ.rationalMatrix h : Matrix n n K) := by
  have hn := σ.pointMatrix_naturality h (𝟙 H.X)
  rw [Category.comp_id] at hn
  ext i j
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom (h.left.appTop _) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      ((σ.pointMatrix _ h : Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of K)))).left, ⊤)) i j)
  rw [hn]
  rfl

/-- On a reduced `H` locally of finite type over an algebraically closed field, a global
function vanishing at every rational point is zero. -/
theorem eq_zero_of_forall_evalPoint_eq_zero [IsAlgClosed K] [IsReduced H.X.left]
    [LocallyOfFiniteType H.X.hom] (f : Γ(H.X.left, ⊤))
    (hf : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X, evalPoint h f = 0) : f = 0 := by
  refine eq_zero_of_forall_appTop_eq_zero H.X.hom f fun q hq => ?_
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom (q.appTop f) = 0 :=
    hf (Over.homMk q hq)
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv h1
  rwa [Iso.hom_inv_id_apply, map_zero] at h2

end Evaluation

section Nilpotence

variable {K : Type u} [Field K] [IsAlgClosed K] {H : GroupScheme (Spec (CommRingCat.of K))}
  [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom] {n : Type} [Fintype n] [DecidableEq n]

/-- If every eigenvalue of every rational point of a connected `H` in a representation `ρ` is an
`m`-th root of unity, then the universal matrix `M` of `ρ` is unipotent over `Γ(H, 𝒪)`. -/
theorem isNilpotent_pointMatrix_sub_one [ConnectedSpace H.X.left] (ρ : MatrixRepresentation H n)
    {m : ℕ} (hm : m ≠ 0)
    (heig : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      ∀ c ∈ (ρ.rationalMatrix h : Matrix n n K).charpoly.roots, c ^ m = 1) :
    IsNilpotent ((ρ.pointMatrix H.X (𝟙 H.X) : Matrix n n Γ(H.X.left, ⊤)) - 1) := by
  let _ : Algebra K Γ(H.X.left, ⊤) := (scalarMap H.X).toAlgebra
  set M := (ρ.pointMatrix H.X (𝟙 H.X) : Matrix n n Γ(H.X.left, ⊤)) with hMdef
  let evA : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) → (Γ(H.X.left, ⊤) →ₐ[K] K) :=
    fun h => { evalPoint h with commutes' := evalPoint_scalarMap h }
  have hevA : ∀ h, (evA h).mapMatrix M = (ρ.rationalMatrix h : Matrix n n K) :=
    fun h => evalPoint_mapMatrix_pointMatrix ρ h
  set Q : K[X] := ((X : K[X]) ^ m - 1) ^ (Fintype.card n + 1) with hQdef
  have hQM : aeval M Q = 0 := by
    ext i j
    rw [Matrix.zero_apply]
    refine eq_zero_of_forall_evalPoint_eq_zero _ fun h => ?_
    have h0 : (evA h).mapMatrix (aeval M Q) = 0 := by
      rw [← aeval_algHom_apply, hevA]
      exact aeval_pow_sub_one_eq_zero _ m (heig h)
    exact congrFun (congrFun h0 i) j
  have hQ0 : Q ≠ 0 := by
    refine pow_ne_zero _ ?_
    have := X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hm) (1 : K)
    rwa [map_one] at this
  have hQ1 : Q.IsRoot 1 := by
    simp [hQdef, IsRoot]
  obtain ⟨e, R, u, w, hQR, huw, hw1⟩ := exists_unipotent_splitting hQ0 hQ1
  obtain ⟨hE, hME⟩ := splitting_aeval hQR huw hQM
  set E := aeval M (w * R) with hEdef
  have hdet : IsIdempotentElem E.det := by
    rw [IsIdempotentElem, ← Matrix.det_mul, hE.eq]
  have hdet1 : evalPoint 1 E.det = 1 := by
    rw [RingHom.map_det]
    have h1 : (evalPoint 1).mapMatrix E = aeval (1 : Matrix n n K) (w * R) := by
      change (evA 1).mapMatrix (aeval M (w * R)) = _
      rw [← aeval_algHom_apply, hevA, MonoidHom.map_one, Units.val_one]
    have h2 := aeval_algebraMap_apply_eq_algebraMap_eval (A := Matrix n n K) (1 : K) (w * R)
    rw [map_one, hw1, map_one] at h2
    rw [h1, h2, Matrix.det_one]
  have hE1 : E = 1 := by
    rcases eq_zero_or_eq_one_of_isIdempotentElem hdet with h0 | h1
    · rw [h0, map_zero] at hdet1
      exact absurd hdet1 zero_ne_one
    · exact (IsIdempotentElem.iff_eq_one_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det E).2 (h1 ▸ isUnit_one))).1 hE
  refine ⟨e, ?_⟩
  rw [hE1, mul_one] at hME
  exact hME

/-- Under the same hypotheses, every rational point acts unipotently through `ρ`. -/
theorem isNilpotent_rationalMatrix_sub_one [ConnectedSpace H.X.left]
    (ρ : MatrixRepresentation H n) {m : ℕ} (hm : m ≠ 0)
    (heig : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      ∀ c ∈ (ρ.rationalMatrix h : Matrix n n K).charpoly.roots, c ^ m = 1)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :
    IsNilpotent ((ρ.rationalMatrix h : Matrix n n K) - 1) := by
  have := (isNilpotent_pointMatrix_sub_one ρ hm heig).map (evalPoint h).mapMatrix
  rwa [map_sub, map_one, RingHom.mapMatrix_apply, evalPoint_mapMatrix_pointMatrix] at this

end Nilpotence

section Translation

variable {K : Type u} [Field K] {H : GroupScheme (Spec (CommRingCat.of K))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Right translation `g ↦ g h` of `H` by a rational point `h`, as a morphism over the base. -/
def rightTranslation (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) : H.X ⟶ H.X :=
  𝟙 H.X * (toBase H.X ≫ h)

/-- The ring endomorphism of global functions given by right translation. -/
def translationMap (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :
    Γ(H.X.left, ⊤) →+* Γ(H.X.left, ⊤) :=
  (rightTranslation h).left.appTop.hom

theorem translationMap_scalarMap (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) (c : K) :
    translationMap h (scalarMap H.X c) = scalarMap H.X c :=
  scalarMap_naturality (rightTranslation h) c

theorem translationMap_mapMatrix_scalarMap (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)
    (A : Matrix n n K) :
    (translationMap h).mapMatrix ((scalarMap H.X).mapMatrix A) = (scalarMap H.X).mapMatrix A := by
  ext i j
  exact translationMap_scalarMap h (A i j)

/-- Right translation by `h` multiplies the universal matrix on the right by the matrix of
`h`. -/
theorem translationMap_mapMatrix_pointMatrix (σ : MatrixRepresentation H n)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :
    (translationMap h).mapMatrix (σ.pointMatrix H.X (𝟙 H.X) : Matrix n n Γ(H.X.left, ⊤)) =
      (σ.pointMatrix H.X (𝟙 H.X) : Matrix n n Γ(H.X.left, ⊤)) *
        (scalarMap H.X).mapMatrix (σ.rationalMatrix h : Matrix n n K) := by
  have hmul : σ.pointMatrix H.X (rightTranslation h) =
      σ.pointMatrix H.X (𝟙 H.X) * σ.pointMatrix H.X (toBase H.X ≫ h) := map_mul _ _ _
  have hn := σ.pointMatrix_naturality (rightTranslation h) (𝟙 H.X)
  rw [Category.comp_id, hmul] at hn
  rw [← pointMatrix_toBase]
  exact (congrArg (fun g : GL n Γ(H.X.left, ⊤) => (g : Matrix n n Γ(H.X.left, ⊤))) hn).symm

/-- Right translation by `h` multiplies the inverse universal matrix on the left by the matrix
of `h⁻¹`. -/
theorem translationMap_mapMatrix_pointMatrix_inv (σ : MatrixRepresentation H n)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :
    (translationMap h).mapMatrix
        (↑(σ.pointMatrix H.X (𝟙 H.X))⁻¹ : Matrix n n Γ(H.X.left, ⊤)) =
      (scalarMap H.X).mapMatrix (σ.rationalMatrix h⁻¹ : Matrix n n K) *
        (↑(σ.pointMatrix H.X (𝟙 H.X))⁻¹ : Matrix n n Γ(H.X.left, ⊤)) := by
  have hmul : σ.pointMatrix H.X (rightTranslation h) =
      σ.pointMatrix H.X (𝟙 H.X) * σ.pointMatrix H.X (toBase H.X ≫ h) := map_mul _ _ _
  have hn := σ.pointMatrix_naturality (rightTranslation h) (𝟙 H.X)
  rw [Category.comp_id, hmul] at hn
  have hinv : Matrix.GeneralLinearGroup.map (translationMap h) (σ.pointMatrix H.X (𝟙 H.X))⁻¹ =
      σ.pointMatrix H.X (toBase H.X ≫ h⁻¹) * (σ.pointMatrix H.X (𝟙 H.X))⁻¹ := by
    rw [map_inv, translationMap, ← hn, mul_inv_rev, GrpObj.comp_inv, map_inv]
  rw [← pointMatrix_toBase]
  exact congrArg (fun g : GL n Γ(H.X.left, ⊤) => (g : Matrix n n Γ(H.X.left, ⊤))) hinv

end Translation

section Generation

variable {K : Type u} [Field K] {H : GroupScheme (Spec (CommRingCat.of K))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The scalar coordinate functions of the general linear group come from the coordinate
ring. -/
theorem scalarMap_generalLinear (c : K) :
    scalarMap (GeneralLinear.groupScheme n (CommRingCat.of K)).X c =
      (Scheme.ΓSpecIso (CommRingCat.of (GeneralLinear.CoordinateRing n (CommRingCat.of K)))).inv
        (algebraMap K (GeneralLinear.CoordinateRing n (CommRingCat.of K)) c) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec.map (CommRingCat.ofHom
    (algebraMap K (GeneralLinear.CoordinateRing n (CommRingCat.of K))))).appTop) c = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- For a closed embedding `ρ` of an affine `H`, global functions of `H` are generated by the
scalars and the entries of the universal matrix and of its inverse. -/
theorem mem_of_isClosedImmersion [IsAffine H.X.left] (ρ : MatrixRepresentation H n)
    [IsClosedImmersion ρ.hom.hom.left] (L : Subring Γ(H.X.left, ⊤))
    (hC : ∀ c : K, scalarMap H.X c ∈ L)
    (hM : ∀ i j, (ρ.pointMatrix H.X (𝟙 H.X) : Matrix n n Γ(H.X.left, ⊤)) i j ∈ L)
    (hMinv : ∀ i j, (↑(ρ.pointMatrix H.X (𝟙 H.X))⁻¹ : Matrix n n Γ(H.X.left, ⊤)) i j ∈ L)
    (f : Γ(H.X.left, ⊤)) : f ∈ L := by
  have : IsAffine (GeneralLinear.groupScheme n (CommRingCat.of K)).X.left :=
    inferInstanceAs (IsAffine (Spec _))
  obtain ⟨g, rfl⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine ρ.hom.hom.left).2 f
  set iso := Scheme.ΓSpecIso (CommRingCat.of (GeneralLinear.CoordinateRing n (CommRingCat.of K)))
  let φ : GeneralLinear.CoordinateRing n (CommRingCat.of K) →+* Γ(H.X.left, ⊤) :=
    ρ.hom.hom.left.appTop.hom.comp
      (iso.inv.hom : GeneralLinear.CoordinateRing n (CommRingCat.of K) →+*
        Γ((GeneralLinear.groupScheme n (CommRingCat.of K)).X.left, ⊤))
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (iso.hom g)
  have hg : ρ.hom.hom.left.appTop g = φ (GeneralLinear.quotient n (CommRingCat.of K) p) := by
    change _ = ρ.hom.hom.left.appTop (iso.inv (Ideal.Quotient.mk _ p))
    rw [hp]
    exact congrArg _ (iso.hom_inv_id_apply g).symm
  rw [hg]
  clear hg hp
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hCa : GeneralLinear.quotient n (CommRingCat.of K) (MvPolynomial.C a) =
        algebraMap K (GeneralLinear.CoordinateRing n (CommRingCat.of K)) a :=
      (GeneralLinear.quotient n (CommRingCat.of K)).commutes a
    rw [hCa]
    have h := scalarMap_naturality ρ.hom.hom a
    rw [scalarMap_generalLinear] at h
    exact (congrArg (· ∈ L) h).mpr (hC a)
  | add p q hp hq =>
    rw [map_add, map_add]
    exact L.add_mem hp hq
  | mul_X p c hp =>
    rw [map_mul, map_mul]
    refine L.mul_mem hp ?_
    cases c with
    | entry i j =>
      have := hM i j
      rwa [MatrixRepresentation.pointMatrix_apply, Category.id_comp,
        GeneralLinear.pointsEquiv_apply_apply] at this
    | inverseEntry i j =>
      have := hMinv i j
      rwa [MatrixRepresentation.pointMatrix_apply, Category.id_comp,
        GeneralLinear.pointsEquiv_inv_apply] at this

end Generation

section Unipotence

variable {K : Type u} [Field K] [IsAlgClosed K] {H : GroupScheme (Spec (CommRingCat.of K))}

/-- **Unipotence criterion.** A reduced connected affine group scheme `H` locally of finite
type over an algebraically closed field, with commuting rational points and a closed embedding
`ρ` into `GL_N` all of whose rational-point eigenvalues are `m`-th roots of unity (`m ≠ 0`), is
unipotent. -/
theorem isUnipotent_of_eigenvalues [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    [ConnectedSpace H.X.left] [IsAffine H.X.left] {N : Type} [Fintype N] [DecidableEq N]
    (ρ : MatrixRepresentation H N) [IsClosedImmersion ρ.hom.hom.left]
    (hcomm : ∀ h h' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X, Commute h h')
    {m : ℕ} (hm : m ≠ 0)
    (heig : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      ∀ c ∈ (ρ.rationalMatrix h : Matrix N N K).charpoly.roots, c ^ m = 1) :
    IsUnipotent H := by
  have hnil : ∀ (n : Type) [Fintype n] [DecidableEq n] (σ : MatrixRepresentation H n)
      (h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X),
      IsNilpotent ((σ.rationalMatrix h : Matrix n n K) - 1) := by
    intro n _ _ σ h
    have hρ : ∀ h' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
        IsNilpotent ((scalarMap H.X).mapMatrix (ρ.rationalMatrix h' : Matrix N N K) - 1) := by
      intro h'
      have := (isNilpotent_rationalMatrix_sub_one ρ hm heig h').map (scalarMap H.X).mapMatrix
      rwa [map_sub, map_one] at this
    have hL : ∀ f, f ∈ locallyUnipotent (translationMap h) :=
      mem_of_isClosedImmersion ρ (locallyUnipotent (translationMap h))
        (fun c => mem_locallyUnipotent_of_fixed _ (translationMap_scalarMap h c))
        (mem_locallyUnipotent_of_mapMatrix_eq_mul _ _ _ (translationMap_mapMatrix_scalarMap h _)
          (translationMap_mapMatrix_pointMatrix ρ h) (hρ h))
        (mem_locallyUnipotent_of_mapMatrix_eq_mul_left _ _ _
          (translationMap_mapMatrix_scalarMap h _)
          (translationMap_mapMatrix_pointMatrix_inv ρ h) (hρ h⁻¹))
    have hB := isNilpotent_sub_one_of_mapMatrix_eq_mul (translationMap h) _ _
      (σ.pointMatrix H.X (𝟙 H.X)).isUnit (translationMap_mapMatrix_scalarMap h _)
      (translationMap_mapMatrix_pointMatrix σ h) (fun _ _ => hL _)
    have := hB.map (evalPoint (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)).mapMatrix
    rwa [map_sub, map_one, evalPoint_mapMatrix_scalarMap] at this
  intro n _ _ _ σ
  let s : Set (Module.End K (n → K)) :=
    Set.range fun h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X =>
      Matrix.toLinAlgEquiv' ((σ.rationalMatrix h : Matrix n n K) - 1)
  have hscomm : ∀ a ∈ s, ∀ b ∈ s, Commute a b := by
    rintro _ ⟨h, rfl⟩ _ ⟨h', rfl⟩
    refine Commute.map ?_ Matrix.toLinAlgEquiv'
    have hc : Commute (σ.rationalMatrix h : Matrix n n K) (σ.rationalMatrix h') :=
      ((hcomm h h').map σ.rationalMatrix).map (Units.coeHom _)
    exact (hc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have hsnil : ∀ a ∈ s, IsNilpotent a := by
    rintro _ ⟨h, rfl⟩
    exact (hnil n σ h).map Matrix.toLinAlgEquiv'
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_eq_zero s hscomm hsnil
  have hfix : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
      (σ.rationalMatrix h : Matrix n n K) *ᵥ v = v := by
    intro h
    have := hv _ ⟨h, rfl⟩
    rwa [Matrix.toLinAlgEquiv'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  refine ⟨v, hv0, (σ.isFixedVector_iff_universal v).2 ?_⟩
  funext i
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_evalPoint_eq_zero _ fun h => ?_
  have hv' : (evalPoint h ∘ fun j => scalarMap H.X (v j)) = v :=
    funext fun j => evalPoint_scalarMap h (v j)
  rw [map_sub, RingHom.map_mulVec, evalPoint_mapMatrix_pointMatrix, hv', hfix,
    evalPoint_scalarMap, sub_self]

end Unipotence

end Langlands.GroupScheme.CentralIntersection
