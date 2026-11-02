import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Mathlib.LinearAlgebra.RootSystem.Defs

/-! # Root data of split maximal tori, and the root datum of `GL_n` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### The root-datum predicate -/

section IsRootDatumOf

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A Mathlib root datum `P` on the character and cocharacter lattices of `T` is the root datum
of `i : T ⟶ G` when its pairing is `latticePairing T`, its roots are the roots of `i`, and every
reflection `P.reflection α` is the action `χ ↦ σ⁻¹ ≫ χ` of some point normalizing `i` through
some automorphism `σ` of `T`. -/
def IsRootDatumOf {J : Type*} (i : T.toGrp ⟶ G)
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) : Prop :=
  P.toLinearMap = latticePairing T ∧ Set.range P.root = roots i ∧
    ∀ α : J, ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : T ≅ T),
      IsNormalizingPoint i n σ ∧ characterAut σ = P.reflection α

end IsRootDatumOf

namespace GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n]

/-! ### The diagonal torus -/

/-- `GL_n` over `Spec (CommRingCat.of k)` is affine over the base. This restates the published
instance `isAffineHom_groupScheme`, which instance search does not find for bases of the form
`CommRingCat.of k`. -/
instance isAffineHom_groupScheme_of (k : Type u) [CommRing k] :
    IsAffineHom (groupScheme n (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme n _

section DiagonalMatrices

variable (A : Type*) [CommRing A]

/-- The diagonal matrix `diag(tᵢ)` of a family of units indexed by `ULift n`. -/
def diagonalTorusUnits : (ULift.{u} n → Aˣ) →* GL n A :=
  (Units.map (Matrix.diagonalRingHom n A).toMonoidHom).comp
    (MulEquiv.piUnits.symm.toMonoidHom.comp
      (MonoidHom.pi fun i => Pi.evalMonoidHom (fun _ => Aˣ) (ULift.up i)))

theorem coe_diagonalTorusUnits (t : ULift.{u} n → Aˣ) :
    (diagonalTorusUnits n A t : Matrix n n A) = Matrix.diagonal fun i => (t ⟨i⟩ : A) :=
  rfl

variable {n A} in
theorem map_diagonalTorusUnits {B : Type*} [CommRing B] (f : A →+* B) (t : ULift.{u} n → Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagonalTorusUnits n A t) =
      diagonalTorusUnits n B fun i => Units.map f.toMonoidHom (t i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, coe_diagonalTorusUnits, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

end DiagonalMatrices

section DiagonalTorus

variable (R : CommRingCat.{u})

/-- The points of the diagonal torus over a test scheme `T`: a family `(tᵢ)` of units of
`Γ(T, 𝒪_T)` goes to the point of `GL_n` with matrix `diag(tᵢ)`. -/
def diagonalTorusPoints (T : Over (Spec R)) :
    (T ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) →* (T ⟶ (groupScheme n R).X) :=
  (pointsEquiv n R T).symm.toMonoidHom.comp
    ((diagonalTorusUnits n Γ(T.left, ⊤)).comp
      (splitTorus.pointsEquiv (ULift.{u} n) T).toMonoidHom)

variable {n R} in
theorem pointsEquiv_diagonalTorusPoints {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    pointsEquiv n R T (diagonalTorusPoints n R T x) =
      diagonalTorusUnits n Γ(T.left, ⊤) (splitTorus.pointsEquiv (ULift.{u} n) T x) :=
  MulEquiv.apply_symm_apply _ _

variable {n R} in
theorem diagonalTorusPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    diagonalTorusPoints n R T' (a ≫ x) = a ≫ diagonalTorusPoints n R T x := by
  apply (pointsEquiv n R T').injective
  rw [pointsEquiv_naturality, pointsEquiv_diagonalTorusPoints, pointsEquiv_diagonalTorusPoints,
    splitTorus.pointsEquiv_naturality, map_diagonalTorusUnits]
  rfl

/-- The diagonal torus `D_n ⟶ GL_n` over `Spec R`, from the split torus `𝔾_m^n` (indexed by
`ULift n`) with its commutative structure, sending `(tᵢ)` to `diag(tᵢ)` on points over every
test scheme. -/
def diagonalTorus :
    (splitTorus.commGroupScheme (Spec R) (ULift.{u} n)).toGrp ⟶ groupScheme n R :=
  homOfPoints (diagonalTorusPoints n R) (fun {_ _} a x => diagonalTorusPoints_naturality a x)

variable {n R}

/-- On points, the diagonal torus sends `(tᵢ)` to `diag(tᵢ)`. -/
theorem pointsEquiv_diagonalTorus {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    pointsEquiv n R T (x ≫ (diagonalTorus n R).hom.hom) =
      diagonalTorusUnits n Γ(T.left, ⊤) (splitTorus.pointsEquiv (ULift.{u} n) T x) := by
  rw [diagonalTorus, comp_homOfPoints, pointsEquiv_diagonalTorusPoints]

theorem pointsEquiv_diagonalTorus_val {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} n)).X) :
    (pointsEquiv n R T (x ≫ (diagonalTorus n R).hom.hom) : Matrix n n Γ(T.left, ⊤)) =
      Matrix.diagonal fun i => (splitTorus.pointsEquiv (ULift.{u} n) T x ⟨i⟩ : Γ(T.left, ⊤)) := by
  rw [pointsEquiv_diagonalTorus, coe_diagonalTorusUnits]

/-- The diagonal torus is injective on points, hence a monomorphism over `Spec R`. -/
instance mono_diagonalTorus_hom : Mono (diagonalTorus n R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (splitTorus.pointsEquiv (ULift.{u} n) Z).injective
  have h1 := congrArg (pointsEquiv n R Z) hgh
  rw [pointsEquiv_diagonalTorus, pointsEquiv_diagonalTorus] at h1
  funext c
  apply Units.ext
  have h2 := congrArg (fun m : GL n Γ(Z.left, ⊤) => (m : Matrix n n Γ(Z.left, ⊤)) c.down c.down) h1
  simpa only [coe_diagonalTorusUnits, Matrix.diagonal_apply_eq] using h2

/-- The underlying morphism of schemes of the diagonal torus is a monomorphism. -/
instance mono_diagonalTorus_left : Mono (diagonalTorus n R).hom.hom.left :=
  Over.mono_left_of_mono _

/-- A cocharacter of the split torus acting on points by `s ↦ (s ^ eᵢ)ᵢ`, composed with the
diagonal torus, is the published diagonal cocharacter of `e`. -/
theorem comp_diagonalTorus_eq_diagonalCocharacter
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec R) (ULift.{u} n))) (e : n → ℤ)
    (hν : ∀ (T : Over (Spec R)) (x : T ⟶ (Gm (Spec R)).X) (i : n),
      splitTorus.pointsEquiv (ULift.{u} n) T (x ≫ (CommGroupScheme.groupHom ν).hom.hom) ⟨i⟩ =
        Gm.pointsEquiv (Spec R) T x ^ e i) :
    CommGroupScheme.groupHom ν ≫ diagonalTorus n R = diagonalCocharacter n R e := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv n R T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_diagonalTorus,
    pointsEquiv_diagonalCocharacter]
  ext i j
  rw [coe_diagonalTorusUnits, coe_diagonalUnits, Matrix.diagonal_apply, Matrix.diagonal_apply, hν]

/-- Over a domain, the cocharacter `(cocharacterLatticeEquiv k _).symm e` composed with the
diagonal torus is the published diagonal cocharacter `diagonalCocharacter n k e`. -/
theorem cocharacterLatticeEquiv_symm_comp_diagonalTorus (k : Type u) [CommRing k] [IsDomain k]
    (e : n → ℤ) :
    CommGroupScheme.groupHom
        ((splitTorus.cocharacterLatticeEquiv k (ULift.{u} n)).symm fun i => e i.down) ≫
      diagonalTorus n (CommRingCat.of k) = diagonalCocharacter n (CommRingCat.of k) e :=
  comp_diagonalTorus_eq_diagonalCocharacter _ e fun _ x i =>
    congrFun (splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm k (ULift.{u} n) _ x) ⟨i⟩

end DiagonalTorus

/-! ### Coordinates on the lattices of the diagonal torus -/

section Lattices

variable (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift n)

/-- `X^*(D_n) ≃ ℤ^n`: `splitTorus.characterLatticeEquiv` followed by `ULift n ≃ n`. -/
def characterCoordEquiv : characterLattice 𝔻 ≃ₗ[ℤ] (n → ℤ) :=
  (splitTorus.characterLatticeEquiv k (ULift.{u} n)).toIntLinearEquiv.trans
    (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift.symm)

/-- `X_*(D_n) ≃ ℤ^n`: `splitTorus.cocharacterLatticeEquiv` followed by `ULift n ≃ n`. -/
def cocharacterCoordEquiv : cocharacterLattice 𝔻 ≃ₗ[ℤ] (n → ℤ) :=
  (splitTorus.cocharacterLatticeEquiv k (ULift.{u} n)).toIntLinearEquiv.trans
    (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift.symm)

variable {n k}

omit [DecidableEq n] in
theorem characterCoordEquiv_apply (χ : characterLattice 𝔻) (i : n) :
    characterCoordEquiv n k χ i = splitTorus.characterLatticeEquiv k (ULift.{u} n) χ ⟨i⟩ := rfl

omit [DecidableEq n] in
theorem cocharacterCoordEquiv_apply (ν : cocharacterLattice 𝔻) (i : n) :
    cocharacterCoordEquiv n k ν i = splitTorus.cocharacterLatticeEquiv k (ULift.{u} n) ν ⟨i⟩ :=
  rfl

omit [DecidableEq n] in
theorem characterLatticeEquiv_eq (χ : characterLattice 𝔻) :
    splitTorus.characterLatticeEquiv k (ULift.{u} n) χ =
      fun c => characterCoordEquiv n k χ c.down := rfl

omit [DecidableEq n] in
theorem cocharacterLatticeEquiv_eq (ν : cocharacterLattice 𝔻) :
    splitTorus.cocharacterLatticeEquiv k (ULift.{u} n) ν =
      fun c => cocharacterCoordEquiv n k ν c.down := rfl

omit [DecidableEq n] in
/-- In coordinates the pairing is the dot product. -/
theorem latticePairing_coord (χ : characterLattice 𝔻) (ν : cocharacterLattice 𝔻) :
    latticePairing 𝔻 χ ν = ∑ i : n, characterCoordEquiv n k χ i * cocharacterCoordEquiv n k ν i := by
  rw [splitTorus.latticePairing_eq_sum]
  exact (Equiv.sum_comp Equiv.ulift.symm _).symm

end Lattices

/-! ### Roots and coroots in coordinates -/

section Coordinates

variable {n}

/-- The vector `eᵢ - eⱼ` of `ℤ^n` attached to `(i, j)`. -/
def rootCoord (p : n × n) : n → ℤ := Pi.single p.1 1 - Pi.single p.2 1

theorem sum_rootCoord_mul (p : n × n) (y : n → ℤ) :
    ∑ c, rootCoord p c * y c = y p.1 - y p.2 := by
  simp [rootCoord, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

theorem sum_mul_rootCoord (p : n × n) (y : n → ℤ) :
    ∑ c, y c * rootCoord p c = y p.1 - y p.2 := by
  simp_rw [mul_comm (y _)]
  exact sum_rootCoord_mul p y

omit [Fintype n] in
theorem rootCoord_injective :
    Function.Injective fun p : {p : n × n // p.1 ≠ p.2} => rootCoord p.1 := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
  simp only at hab hcd h
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [rootCoord, Pi.sub_apply, Pi.single_apply] at h1 h2
  have hac : a = c := by
    by_contra hac
    split_ifs at h1 h2 <;> simp_all
  have hbd : b = d := by
    by_contra hbd
    split_ifs at h1 h2 <;> simp_all
  subst hac hbd
  rfl

omit [Fintype n] in
/-- The reflection along `eᵢ - eⱼ` swaps the coordinates `i` and `j`. -/
theorem sub_smul_rootCoord {i j : n} (hij : i ≠ j) (x : n → ℤ) :
    x - (x i - x j) • rootCoord (i, j) = x ∘ Equiv.swap i j := by
  funext c
  simp only [rootCoord, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;> omega

omit [Fintype n] in
theorem rootCoord_swap (i j : n) (p : n × n) :
    rootCoord (Equiv.swap i j p.1, Equiv.swap i j p.2) = rootCoord p ∘ Equiv.swap i j := by
  funext c
  simp only [rootCoord, Pi.sub_apply, Pi.single_apply, Function.comp_apply,
    Equiv.swap_apply_eq_iff]

/-- The permutation of `{(i, j) | i ≠ j}` induced by the transposition of the coordinates of
`p`. -/
def reflectionPermEquiv (p : {p : n × n // p.1 ≠ p.2}) :
    {p : n × n // p.1 ≠ p.2} ≃ {p : n × n // p.1 ≠ p.2} :=
  Equiv.subtypeEquiv ((Equiv.swap p.1.1 p.1.2).prodCongr (Equiv.swap p.1.1 p.1.2))
    fun _ => (Equiv.swap p.1.1 p.1.2).injective.ne_iff.symm

omit [Fintype n] in
theorem reflectionPermEquiv_apply (p q : {p : n × n // p.1 ≠ p.2}) :
    (reflectionPermEquiv p q).1 = (Equiv.swap p.1.1 p.1.2 q.1.1, Equiv.swap p.1.1 p.1.2 q.1.2) :=
  rfl

end Coordinates

/-! ### The root datum of `GL_n` -/

section RootDatum

variable (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift n)

/-- The root datum of `GL_n` with its diagonal torus over a field: roots `eᵢ - eⱼ` and coroots
`eᵢ^∨ - eⱼ^∨` for `i ≠ j`, in the coordinates of `characterLatticeEquiv` and
`cocharacterLatticeEquiv`, with pairing `latticePairing`. -/
def rootDatum : RootDatum {p : n × n // p.1 ≠ p.2} (characterLattice 𝔻) (cocharacterLattice 𝔻) where
  toLinearMap := latticePairing 𝔻
  isPerfPair_toLinearMap := splitTorus.isPerfPair_latticePairing k (ULift.{u} n)
  root := ⟨fun p => (characterCoordEquiv n k).symm (rootCoord p.1),
    (characterCoordEquiv n k).symm.injective.comp rootCoord_injective⟩
  coroot := ⟨fun p => (cocharacterCoordEquiv n k).symm (rootCoord p.1),
    (cocharacterCoordEquiv n k).symm.injective.comp rootCoord_injective⟩
  root_coroot_two p := by
    change latticePairing 𝔻 ((characterCoordEquiv n k).symm (rootCoord p.1))
      ((cocharacterCoordEquiv n k).symm (rootCoord p.1)) = 2
    rw [latticePairing_coord, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      sum_rootCoord_mul]
    simp [rootCoord, p.2, p.2.symm]
  reflectionPerm := reflectionPermEquiv
  reflectionPerm_root p q := by
    change (characterCoordEquiv n k).symm (rootCoord q.1) -
        latticePairing 𝔻 ((characterCoordEquiv n k).symm (rootCoord q.1))
          ((cocharacterCoordEquiv n k).symm (rootCoord p.1)) •
          (characterCoordEquiv n k).symm (rootCoord p.1) =
      (characterCoordEquiv n k).symm (rootCoord (reflectionPermEquiv p q).1)
    apply (characterCoordEquiv n k).injective
    rw [map_sub, map_zsmul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, latticePairing_coord, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, sum_mul_rootCoord, reflectionPermEquiv_apply,
      rootCoord_swap]
    exact sub_smul_rootCoord p.2 _
  reflectionPerm_coroot p q := by
    change (cocharacterCoordEquiv n k).symm (rootCoord q.1) -
        latticePairing 𝔻 ((characterCoordEquiv n k).symm (rootCoord p.1))
          ((cocharacterCoordEquiv n k).symm (rootCoord q.1)) •
          (cocharacterCoordEquiv n k).symm (rootCoord p.1) =
      (cocharacterCoordEquiv n k).symm (rootCoord (reflectionPermEquiv p q).1)
    apply (cocharacterCoordEquiv n k).injective
    rw [map_sub, map_zsmul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, latticePairing_coord, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, sum_rootCoord_mul, reflectionPermEquiv_apply,
      rootCoord_swap]
    exact sub_smul_rootCoord p.2 _

variable {n k}

theorem rootDatum_toLinearMap : (rootDatum n k).toLinearMap = latticePairing 𝔻 := rfl

theorem characterCoordEquiv_rootDatum_root (p : {p : n × n // p.1 ≠ p.2}) :
    characterCoordEquiv n k ((rootDatum n k).root p) = rootCoord p.1 :=
  LinearEquiv.apply_symm_apply _ _

theorem cocharacterCoordEquiv_rootDatum_coroot (p : {p : n × n // p.1 ≠ p.2}) :
    cocharacterCoordEquiv n k ((rootDatum n k).coroot p) = rootCoord p.1 :=
  LinearEquiv.apply_symm_apply _ _

/-- Under `characterLatticeEquiv` the root of `(i, j)` is `eᵢ - eⱼ`. -/
theorem characterLatticeEquiv_rootDatum_root (p : {p : n × n // p.1 ≠ p.2}) :
    splitTorus.characterLatticeEquiv k (ULift.{u} n) ((rootDatum n k).root p) =
      Pi.single (ULift.up p.1.1) 1 - Pi.single (ULift.up p.1.2) 1 := by
  rw [characterLatticeEquiv_eq, characterCoordEquiv_rootDatum_root]
  funext c
  simp only [rootCoord, Pi.sub_apply, Pi.single_apply, ULift.ext_iff]

/-- Under `cocharacterLatticeEquiv` the coroot of `(i, j)` is `eᵢ^∨ - eⱼ^∨`. -/
theorem cocharacterLatticeEquiv_rootDatum_coroot (p : {p : n × n // p.1 ≠ p.2}) :
    splitTorus.cocharacterLatticeEquiv k (ULift.{u} n) ((rootDatum n k).coroot p) =
      Pi.single (ULift.up p.1.1) 1 - Pi.single (ULift.up p.1.2) 1 := by
  rw [cocharacterLatticeEquiv_eq, cocharacterCoordEquiv_rootDatum_coroot]
  funext c
  simp only [rootCoord, Pi.sub_apply, Pi.single_apply, ULift.ext_iff]

end RootDatum

/-! ### The permutation action -/

section Permutation

variable (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift n)

/-- The action of `S_n` on `X^*(D_n)` permuting coordinates: `w` sends the character with
coordinates `m` to the one with coordinates `m ∘ w⁻¹`. -/
def permutationAction : Equiv.Perm n →* (characterLattice 𝔻 ≃ₗ[ℤ] characterLattice 𝔻) where
  toFun w := ((characterCoordEquiv n k).trans (LinearEquiv.funCongrLeft ℤ ℤ w⁻¹)).trans
    (characterCoordEquiv n k).symm
  map_one' := by
    apply LinearEquiv.ext
    intro χ
    apply (characterCoordEquiv n k).injective
    funext c
    simp [LinearEquiv.funCongrLeft_apply]
  map_mul' w w' := by
    apply LinearEquiv.ext
    intro χ
    apply (characterCoordEquiv n k).injective
    funext c
    simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, mul_inv_rev]

variable {n k}

omit [DecidableEq n] in
theorem characterCoordEquiv_permutationAction (w : Equiv.Perm n) (χ : characterLattice 𝔻)
    (c : n) : characterCoordEquiv n k (permutationAction n k w χ) c =
      characterCoordEquiv n k χ (w⁻¹ c) := by
  simp [permutationAction, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

omit [DecidableEq n] in
/-- Under `characterLatticeEquiv`, `permutationAction w` permutes the coordinates by `w`. -/
theorem characterLatticeEquiv_permutationAction (w : Equiv.Perm n) (χ : characterLattice 𝔻) :
    splitTorus.characterLatticeEquiv k (ULift.{u} n) (permutationAction n k w χ) =
      fun c => splitTorus.characterLatticeEquiv k (ULift.{u} n) χ ⟨w⁻¹ c.down⟩ := by
  funext c
  exact characterCoordEquiv_permutationAction w χ c.down

/-- The reflection of the root `eᵢ - eⱼ` is the permutation action of the transposition
`(i j)`. -/
theorem rootDatum_reflection (p : {p : n × n // p.1 ≠ p.2}) :
    (rootDatum n k).reflection p = permutationAction n k (Equiv.swap p.1.1 p.1.2) := by
  apply LinearEquiv.ext
  intro χ
  apply (characterCoordEquiv n k).injective
  rw [RootPairing.reflection_apply]
  change characterCoordEquiv n k (χ - latticePairing 𝔻 χ ((rootDatum n k).coroot p) •
    (rootDatum n k).root p) = _
  rw [map_sub, map_zsmul, characterCoordEquiv_rootDatum_root, latticePairing_coord,
    cocharacterCoordEquiv_rootDatum_coroot, sum_mul_rootCoord, sub_smul_rootCoord p.2]
  funext c
  rw [characterCoordEquiv_permutationAction, Equiv.swap_inv]
  rfl

end Permutation

end GeneralLinear

end Langlands.GroupScheme
