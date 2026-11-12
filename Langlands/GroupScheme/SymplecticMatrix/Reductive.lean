import Langlands.GroupScheme.SymplecticMatrix.Smooth
import Langlands.GroupScheme.SymplecticMatrix.Generation
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Torus.SolvableFixedAlgClosedCore
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.BaseChangeReflection

/-! # The split symplectic group is reductive

The split symplectic group scheme `SymplecticMatrix.groupScheme l R` is a connected reductive
group over every field (`isConnectedReductive`) and a reductive group scheme over every
commutative ring (`isReductive`).

Connectedness over an algebraically closed field: by the big-cell decomposition every rational
point is a product of rational points of the images of the general linear group (Levi embedding)
and of additive groups (`t ↦ upper (t • S)`, `t ↦ lower (t • S)` for symmetric `S`), all of
which are connected, so every rational point lies in the identity component. Triviality of the
unipotent radical: the fixed vectors of a normal unipotent subgroup form a nonzero subspace
stable under all symplectic matrices, hence everything.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

section Homs

/-- The Levi embedding `A ↦ levi A` as a group homomorphism. -/
def leviHom (A : Type*) [CommRing A] : GL l A →* Matrix.symplecticGroup l A where
  toFun g := ⟨levi g, levi_mem g⟩
  map_one' := Subtype.ext (by simp [levi, fromBlocks_one])
  map_mul' g h := Subtype.ext (levi_mul g h)

@[simp] theorem coe_leviHom {A : Type*} [CommRing A] (g : GL l A) :
    ((leviHom A g : Matrix.symplecticGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) = levi g := rfl

/-- The upper unipotent homomorphism `t ↦ upper (t • φ(S))` of a symmetric matrix `S`, on the
additive group of a ring `A` with a ring map `φ` from the coefficients of `S`. -/
def upperHom {B : Type*} [CommRing B] {S : Matrix l l B} (hS : S.IsSymm) {A : Type*} [CommRing A]
    (φ : B →+* A) : Multiplicative (Fin 1 → A) →* Matrix.symplecticGroup l A where
  toFun t := ⟨upper (t.toAdd 0 • S.map φ), upper_mem ((hS.map _).smul _)⟩
  map_one' := Subtype.ext (by simp [upper_zero])
  map_mul' s t := Subtype.ext (by simp [upper_mul_upper, add_smul])

/-- The lower unipotent homomorphism `t ↦ lower (t • φ(S))` of a symmetric matrix `S`, on the
additive group of a ring `A` with a ring map `φ` from the coefficients of `S`. -/
def lowerHom {B : Type*} [CommRing B] {S : Matrix l l B} (hS : S.IsSymm) {A : Type*} [CommRing A]
    (φ : B →+* A) : Multiplicative (Fin 1 → A) →* Matrix.symplecticGroup l A where
  toFun t := ⟨lower (t.toAdd 0 • S.map φ), lower_mem ((hS.map _).smul _)⟩
  map_one' := Subtype.ext (by simp [lower_zero])
  map_mul' s t := Subtype.ext (by simp [lower_mul_lower, add_smul])

@[simp] theorem coe_upperHom {B : Type*} [CommRing B] {S : Matrix l l B} (hS : S.IsSymm)
    {A : Type*} [CommRing A] (φ : B →+* A) (t : Multiplicative (Fin 1 → A)) :
    ((upperHom hS φ t : Matrix.symplecticGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) =
      upper (t.toAdd 0 • S.map φ) := rfl

@[simp] theorem coe_lowerHom {B : Type*} [CommRing B] {S : Matrix l l B} (hS : S.IsSymm)
    {A : Type*} [CommRing A] (φ : B →+* A) (t : Multiplicative (Fin 1 → A)) :
    ((lowerHom hS φ t : Matrix.symplecticGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) =
      lower (t.toAdd 0 • S.map φ) := rfl

variable (R : CommRingCat.{u})

omit [Fintype l] [DecidableEq l] in
theorem smul_map_algebraMap {S : Matrix l l R} {A B : CommAlgCat.{u} R} (f : A ⟶ B) (t : A) :
    (t • S.map (algebraMap R A)).map f.hom.toRingHom = f.hom t • S.map (algebraMap R B) := by
  ext i j
  simp

/-- The Levi embedding as a natural transformation. -/
def leviTrans : GeneralLinear.functor l R ⟶ functor l R where
  app A := GrpCat.ofHom (leviHom A)
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    exact (map_levi f.hom.toRingHom g).symm

/-- The upper unipotent homomorphism of a symmetric matrix as a natural transformation. -/
def upperTrans {S : Matrix l l R} (hS : S.IsSymm) : VectorGroup.functor R 1 ⟶ functor l R where
  app A := GrpCat.ofHom (upperHom hS (algebraMap R A))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    exact (congrArg upper (smul_map_algebraMap R f (t.toAdd 0))).symm.trans
      (map_upper f.hom.toRingHom _).symm

/-- The lower unipotent homomorphism of a symmetric matrix as a natural transformation. -/
def lowerTrans {S : Matrix l l R} (hS : S.IsSymm) : VectorGroup.functor R 1 ⟶ functor l R where
  app A := GrpCat.ofHom (lowerHom hS (algebraMap R A))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    exact (congrArg lower (smul_map_algebraMap R f (t.toAdd 0))).symm.trans
      (map_lower f.hom.toRingHom _).symm

/-- The Levi embedding `GL_l → Sp_{2l}` of group schemes. -/
def leviMap : GeneralLinear.groupScheme l R ⟶ groupScheme l R :=
  Corepresented.groupSchemeMap (GeneralLinear.corepresentableBy l R) (corepresentableBy l R)
    (leviTrans R)

/-- The upper unipotent homomorphism `𝔾ₐ → Sp_{2l}` of a symmetric matrix. -/
def upperMap {S : Matrix l l R} (hS : S.IsSymm) :
    VectorGroup.groupScheme R 1 ⟶ groupScheme l R :=
  Corepresented.groupSchemeMap (VectorGroup.corepresentableBy R 1) (corepresentableBy l R)
    (upperTrans R hS)

/-- The lower unipotent homomorphism `𝔾ₐ → Sp_{2l}` of a symmetric matrix. -/
def lowerMap {S : Matrix l l R} (hS : S.IsSymm) :
    VectorGroup.groupScheme R 1 ⟶ groupScheme l R :=
  Corepresented.groupSchemeMap (VectorGroup.corepresentableBy R 1) (corepresentableBy l R)
    (lowerTrans R hS)

variable {R}

theorem pointsEquiv_leviMap (T : Over (Spec R)) (x : T ⟶ (GeneralLinear.groupScheme l R).X) :
    pointsEquiv l R T (x ≫ (leviMap R).hom.hom) =
      leviHom _ (GeneralLinear.pointsEquiv l R T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

theorem pointsEquiv_upperMap {S : Matrix l l R} (hS : S.IsSymm) (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    pointsEquiv l R T (x ≫ (upperMap R hS).hom.hom) =
      upperHom hS (scalarMap T) (VectorGroup.coordinates R 1 T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

theorem pointsEquiv_lowerMap {S : Matrix l l R} (hS : S.IsSymm) (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    pointsEquiv l R T (x ≫ (lowerMap R hS).hom.hom) =
      lowerHom hS (scalarMap T) (VectorGroup.coordinates R 1 T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

end Homs

section Connected

variable {k : Type u} [Field k]

instance connectedSpace_vectorGroup :
    ConnectedSpace (VectorGroup.groupScheme (CommRingCat.of k) 1).X.left := by
  change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
  infer_instance

/-- A point that factors through a homomorphism from a connected group scheme lies in the
identity component. -/
theorem comp_mem_range_identityComponentι {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace H.X.left] (φ : H ⟶ G)
    {T : Over (Spec (CommRingCat.of k))} (z : T ⟶ H.X) :
    z ≫ φ.hom.hom ∈ (SubgroupFunctor.range (identityComponentι G)).carrier T := by
  refine SubgroupFunctor.mem_range.2 ⟨z ≫ (IdentityComponent.factor G φ).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IdentityComponent.factor_identityComponentι]

variable (l) in
/-- Over an algebraically closed field the split symplectic group is connected. -/
theorem connectedSpace_groupScheme_of_isAlgClosed [IsAlgClosed k] :
    ConnectedSpace (groupScheme l (CommRingCat.of k)).X.left := by
  have := smooth_groupScheme l (CommRingCat.of k)
  have := isAffineHom_groupScheme l (CommRingCat.of k)
  refine IdentityComponent.connectedSpace_of_forall_mem_range fun x => ?_
  let T₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let e : k ≃+* Γ(T₀.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have hψ : ∀ a : k, scalarMap T₀ a = e a := fun a => by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (𝟙 (Spec (CommRingCat.of k)) : Spec (CommRingCat.of k) ⟶ _).appTop).hom a = _
    rw [Scheme.Hom.id_appTop, Category.comp_id]
    rfl
  let M := pointsEquiv l _ T₀ x
  let M₀ : Matrix.symplecticGroup l k := map l e.symm.toRingHom M
  have hM : (M : Matrix (l ⊕ l) (l ⊕ l) Γ(T₀.left, ⊤)) =
      (M₀ : Matrix (l ⊕ l) (l ⊕ l) k).map e := by
    ext i j
    simp [M₀]
  obtain ⟨X, Z, Y, hX, hZ, hY, A, hM₀⟩ := exists_eq_upper_mul_lower_mul_levi_mul_upper M₀.2
  let one : T₀ ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X :=
    (VectorGroup.coordinates _ 1 T₀).symm (Multiplicative.ofAdd fun _ => 1)
  let a : T₀ ⟶ (GeneralLinear.groupScheme l (CommRingCat.of k)).X :=
    (GeneralLinear.pointsEquiv l _ T₀).symm (GeneralLinearGroup.map e.toRingHom A)
  have hone : (VectorGroup.coordinates (CommRingCat.of k) 1 T₀ one).toAdd 0 = 1 := by
    simp only [one, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hU : ∀ (W : Matrix l l k) (hW : W.IsSymm),
      ((upperHom hW (scalarMap T₀) (VectorGroup.coordinates _ 1 T₀ one) :
        Matrix.symplecticGroup l Γ(T₀.left, ⊤)) : Matrix (l ⊕ l) (l ⊕ l) Γ(T₀.left, ⊤)) =
        upper (W.map e) := by
    intro W hW
    rw [coe_upperHom, hone, one_smul]
    exact congrArg upper (Matrix.ext fun i j => hψ (W i j))
  have hL : ∀ (W : Matrix l l k) (hW : W.IsSymm),
      ((lowerHom hW (scalarMap T₀) (VectorGroup.coordinates _ 1 T₀ one) :
        Matrix.symplecticGroup l Γ(T₀.left, ⊤)) : Matrix (l ⊕ l) (l ⊕ l) Γ(T₀.left, ⊤)) =
        lower (W.map e) := by
    intro W hW
    rw [coe_lowerHom, hone, one_smul]
    exact congrArg lower (Matrix.ext fun i j => hψ (W i j))
  have hLevi : ((leviHom Γ(T₀.left, ⊤) (GeneralLinear.pointsEquiv l _ T₀ a) :
      Matrix.symplecticGroup l Γ(T₀.left, ⊤)) : Matrix (l ⊕ l) (l ⊕ l) Γ(T₀.left, ⊤)) =
      levi (GeneralLinearGroup.map e.toRingHom A) := by
    simp only [a, MulEquiv.apply_symm_apply, coe_leviHom]
  have hx : x = (one ≫ (upperMap _ hX).hom.hom) * (one ≫ (lowerMap _ hZ).hom.hom) *
      (a ≫ (leviMap _).hom.hom) * (one ≫ (upperMap _ hY).hom.hom) := by
    apply (pointsEquiv l _ T₀).injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_mul, pointsEquiv_upperMap, pointsEquiv_lowerMap,
      pointsEquiv_leviMap, pointsEquiv_upperMap, Submonoid.coe_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, hU X hX, hL Z hZ, hLevi, hU Y hY]
    change (M : Matrix (l ⊕ l) (l ⊕ l) Γ(T₀.left, ⊤)) = _
    rw [hM, hM₀, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    rw [show ((upper X).map e) = upper (X.map e) from map_upper e.toRingHom X,
      show ((lower Z).map e) = lower (Z.map e) from map_lower e.toRingHom Z,
      show ((levi A).map e) = levi (GeneralLinearGroup.map e.toRingHom A) from
        map_levi e.toRingHom A,
      show ((upper Y).map e) = upper (Y.map e) from map_upper e.toRingHom Y]
  rw [hx]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact comp_mem_range_identityComponentι (upperMap _ hX) one
  · exact comp_mem_range_identityComponentι (lowerMap _ hZ) one
  · exact comp_mem_range_identityComponentι (leviMap _) a
  · exact comp_mem_range_identityComponentι (upperMap _ hY) one

variable (l k) in
/-- The split symplectic group over a field is connected. -/
theorem connectedSpace_groupScheme :
    ConnectedSpace (groupScheme l (CommRingCat.of k)).X.left := by
  let b := toAlgebraicClosure k
  have : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  refine connectedSpace_of_baseChange b _ ?_
  have : ConnectedSpace (groupScheme l (CommRingCat.of (AlgebraicClosure k))).X.left :=
    connectedSpace_groupScheme_of_isAlgClosed l
  exact DynamicConnected.connectedSpace_of_iso (baseChangeModelIso l b)

end Connected

section Radical

variable {K : Type u} [Field K]

/-- The symplectic point obtained from a symplectic matrix over the base field. -/
def constantPoint (T : Over (Spec (CommRingCat.of K))) (g : Matrix.symplecticGroup l K) :
    T ⟶ (groupScheme l (CommRingCat.of K)).X :=
  (pointsEquiv l _ T).symm (map l (scalarMap T) g)

/-- Normality in the symplectic group preserves the standard fixed subspace. -/
theorem mulVec_mem_fixedSubmodule {H : GroupScheme (Spec (CommRingCat.of K))}
    (i : H ⟶ groupScheme l (CommRingCat.of K))
    (hN : (SubgroupFunctor.range i).IsNormal) (g : Matrix.symplecticGroup l K)
    {v : l ⊕ l → K} (hv : v ∈ MatrixRepresentation.fixedSubmodule
      (i ≫ inclusion l (CommRingCat.of K))) :
    (g : Matrix (l ⊕ l) (l ⊕ l) K) *ᵥ v ∈ MatrixRepresentation.fixedSubmodule
      (i ≫ inclusion l (CommRingCat.of K)) := by
  intro T h
  obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.1
    (hN T (constantPoint T g)⁻¹ (h ≫ i.hom.hom) trivial
      (SubgroupFunctor.mem_range.2 ⟨h, rfl⟩))
  have key := hv T h'
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion, hh'] at key
  simp only [map_mul, map_inv, inv_inv] at key
  rw [MatrixRepresentation.pointMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion]
  have hg : (fun j => scalarMap T (((g : Matrix (l ⊕ l) (l ⊕ l) K) *ᵥ v) j)) =
      ((pointsEquiv l _ T (constantPoint T g) : Matrix.symplecticGroup l Γ(T.left, ⊤)) :
        Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j)) := by
    funext j
    rw [RingHom.map_mulVec, constantPoint, MulEquiv.apply_symm_apply]
    rfl
  rw [hg]
  set G := toGL (pointsEquiv l _ T (constantPoint T g))
  set M := toGL (pointsEquiv l _ T (h ≫ i.hom.hom))
  have e1 : (M : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
      ((G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j))) =
      (G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
        (((G⁻¹ * M * G : GL (l ⊕ l) Γ(T.left, ⊤)) : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
          (fun j => scalarMap T (v j))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  change (M : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ
    ((G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j))) =
      (G : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *ᵥ (fun j => scalarMap T (v j))
  rw [e1, key]

variable (K l) in
/-- Every smooth connected unipotent normal closed subgroup of the split symplectic group over a
field is trivial. -/
theorem hasTrivialUnipotentRadical :
    HasTrivialUnipotentRadical (groupScheme l (CommRingCat.of K)) := by
  intro H i _ _ _ hU hN
  have hfix : ∀ (T : Over (Spec (CommRingCat.of K))) (h : T ⟶ H.X),
      pointsEquiv l _ T (h ≫ i.hom.hom) = 1 := by
    intro T h
    apply ext
    intro a b
    rcases isEmpty_or_nonempty l with hl | hl
    · exact isEmptyElim (a.elim id id)
    let ρ := i ≫ inclusion l (CommRingCat.of K)
    obtain ⟨v, hv0, hv⟩ := hU (l ⊕ l) ρ
    have htop := eq_top_of_forall_mulVec_mem (MatrixRepresentation.fixedSubmodule ρ)
      (fun g hg w hw => mulVec_mem_fixedSubmodule i hN ⟨g, hg⟩ hw)
      ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩)
    have hb : Pi.single b (1 : K) ∈ MatrixRepresentation.fixedSubmodule ρ := by
      rw [htop]
      exact Submodule.mem_top
    have hb' := hb T h
    have hs : (fun j => scalarMap T ((Pi.single b (1 : K) : l ⊕ l → K) j)) =
        Pi.single b 1 := by
      funext j
      by_cases hj : j = b
      · subst hj
        simp
      · simp [hj]
    rw [hs, Matrix.mulVec_single_one, MatrixRepresentation.pointMatrix_apply] at hb'
    change _ = _ at hb'
    dsimp only [ρ] at hb'
    rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_inclusion] at hb'
    have := congrFun hb' a
    by_cases hab : a = b
    · subst hab
      simpa [Matrix.col] using this
    · simpa [Matrix.col, hab, Matrix.one_apply_ne hab] using this
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    apply (pointsEquiv l _ T).injective
    rw [hfix, map_one]
  · rintro rfl
    exact Subgroup.one_mem _

end Radical

section Reductive

variable (K : Type u) [Field K] (l)

/-- The split symplectic group over a field is pseudo-reductive. -/
theorem isPseudoReductive : IsPseudoReductive (groupScheme l (CommRingCat.of K)) where
  smooth := smooth_groupScheme l _
  isAffineHom := isAffineHom_groupScheme l _
  connectedSpace := connectedSpace_groupScheme l K
  hasTrivialUnipotentRadical := hasTrivialUnipotentRadical l K

/-- The split symplectic group over a field is connected reductive. -/
theorem isConnectedReductive : IsConnectedReductive (groupScheme l (CommRingCat.of K)) where
  smooth := smooth_groupScheme l _
  isAffineHom := isAffineHom_groupScheme l _
  connectedSpace := connectedSpace_groupScheme l K
  hasTrivialGeometricUnipotentRadical :=
    HasTrivialUnipotentRadical.of_iso (baseChangeModelIso l (toAlgebraicClosure K))
      (hasTrivialUnipotentRadical l (AlgebraicClosure K))

/-- The split symplectic group scheme over every commutative ring is reductive. -/
theorem isReductive (R : CommRingCat.{u}) : IsReductive (groupScheme l R) where
  smooth := smooth_groupScheme l R
  isAffineHom := isAffineHom_groupScheme l R
  geometricFiber s :=
    IsPseudoReductive.of_iso (baseChangeModelIso l (geometricPoint (Spec R) s))
      (isPseudoReductive l _)

end Reductive

end Langlands.GroupScheme.SymplecticMatrix
