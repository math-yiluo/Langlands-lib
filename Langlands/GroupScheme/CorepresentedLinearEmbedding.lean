import Langlands.GroupScheme.ComoduleMatrixCoefficients
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Closed linear embeddings of corepresented affine group schemes over a field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.Corepresented

namespace LinearEmbedding

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section Coalgebra

/-- The point of `F` classified by an algebra map out of `B`. -/
def pt {S : CommAlgCat.{u} R} (f : B ⟶ S) : F.obj S := e.homEquiv f

/-- The algebra map out of `B` classifying a point of `F`. -/
def cls {S : CommAlgCat.{u} R} (x : F.obj S) : B ⟶ S := e.homEquiv.symm x

@[simp] theorem pt_cls {S : CommAlgCat.{u} R} (x : F.obj S) : pt e (cls e x) = x :=
  e.homEquiv.apply_symm_apply x

@[simp] theorem cls_pt {S : CommAlgCat.{u} R} (f : B ⟶ S) : cls e (pt e f) = f :=
  e.homEquiv.symm_apply_apply f

theorem pt_comp {S T : CommAlgCat.{u} R} (f : B ⟶ S) (g : S ⟶ T) :
    pt e (f ≫ g) = F.map g (pt e f) :=
  e.homEquiv_comp g f

theorem cls_map {S T : CommAlgCat.{u} R} (x : F.obj S) (g : S ⟶ T) :
    cls e (F.map g x) = cls e x ≫ g := by
  rw [← pt_cls e x, ← pt_comp, cls_pt, cls_pt]

variable (B) in
/-- The tensor square of the representing algebra. -/
abbrev sq : CommAlgCat.{u} R := CommAlgCat.of R (B ⊗[R] B)

variable (B) in
/-- The left inclusion `b ↦ b ⊗ 1`. -/
def inl : B ⟶ sq B := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft

variable (B) in
/-- The right inclusion `b ↦ 1 ⊗ b`. -/
def inr : B ⟶ sq B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight

/-- The algebra map out of the tensor square determined by two algebra maps. -/
def pair {S : CommAlgCat.{u} R} (f g : B ⟶ S) : sq B ⟶ S :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift f.hom g.hom fun _ _ => Commute.all _ _)

@[simp] theorem pair_tmul {S : CommAlgCat.{u} R} (f g : B ⟶ S) (x y : B) :
    (pair f g).hom (x ⊗ₜ[R] y) = f.hom x * g.hom y := by
  simp [pair]

theorem inl_pair {S : CommAlgCat.{u} R} (f g : B ⟶ S) : inl B ≫ pair f g = f := by
  ext x
  simp [inl, pair]

theorem inr_pair {S : CommAlgCat.{u} R} (f g : B ⟶ S) : inr B ≫ pair f g = g := by
  ext x
  simp [inr, pair]

/-- The comultiplication: the algebra map classifying the product of the two universal points. -/
def comul : B ⟶ sq B := cls e (pt e (inl B) * pt e (inr B))

/-- The product of two points is classified by the comultiplication followed by the pair map. -/
theorem pt_mul {S : CommAlgCat.{u} R} (f g : B ⟶ S) :
    pt e f * pt e g = pt e (comul e ≫ pair f g) := by
  rw [pt_comp, comul, pt_cls, map_mul, ← pt_comp, ← pt_comp, inl_pair, inr_pair]

theorem cls_mul {S : CommAlgCat.{u} R} (x y : F.obj S) :
    cls e (x * y) = comul e ≫ pair (cls e x) (cls e y) := by
  rw [← pt_cls e x, ← pt_cls e y, pt_mul, cls_pt, cls_pt, cls_pt]

/-- The base ring as a test algebra. -/
abbrev base : CommAlgCat.{u} R := CommAlgCat.of R R

/-- The structure map of a test algebra. -/
def unitMap (S : CommAlgCat.{u} R) : base ⟶ S := CommAlgCat.ofHom (Algebra.ofId R S)

/-- The counit: the algebra map classifying the identity point over the base ring. -/
def counit : B ⟶ base := cls e 1

theorem cls_one (S : CommAlgCat.{u} R) : cls e (1 : F.obj S) = counit e ≫ unitMap S := by
  apply e.homEquiv.injective
  change pt e (cls e 1) = pt e (counit e ≫ unitMap S)
  rw [pt_cls, pt_comp, counit, pt_cls, map_one]

/-- The comultiplication as a linear map. -/
def comulL : B →ₗ[R] B ⊗[R] B := (comul e).hom.toLinearMap

/-- The counit as a linear map. -/
def counitL : B →ₗ[R] R := (counit e).hom.toLinearMap

theorem comulL_apply (x : B) : comulL e x = (comul e).hom x := rfl

theorem counitL_apply (x : B) : counitL e x = (counit e).hom x := rfl

theorem rightCounit : Comodule.RightCounit (comulL e) (counitL e) := by
  have h : comul e ≫ pair (𝟙 B) (counit e ≫ unitMap B) = 𝟙 B := by
    have := cls_mul e (pt e (𝟙 B)) 1
    rw [mul_one, cls_pt, cls_one] at this
    exact this.symm
  have hz : ∀ z : B ⊗[R] B, TensorProduct.rid R B ((counitL e).lTensor B z) =
      (pair (𝟙 B) (counit e ≫ unitMap B)).hom z := by
    intro z
    induction z with
    | tmul p q =>
      rw [pair_tmul]
      simp [counitL, unitMap, Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe, id]
  rw [hz, comulL_apply, ← CommAlgCat.comp_apply, h]
  rfl

theorem leftCounit : Comodule.LeftCounit (comulL e) (counitL e) := by
  have h : comul e ≫ pair (counit e ≫ unitMap B) (𝟙 B) = 𝟙 B := by
    have := cls_mul e 1 (pt e (𝟙 B))
    rw [one_mul, cls_pt, cls_one] at this
    exact this.symm
  have hz : ∀ z : B ⊗[R] B, TensorProduct.lid R B ((counitL e).rTensor B z) =
      (pair (counit e ≫ unitMap B) (𝟙 B)).hom z := by
    intro z
    induction z with
    | tmul p q =>
      rw [pair_tmul]
      simp [counitL, unitMap, Algebra.smul_def]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe, id]
  rw [hz, comulL_apply, ← CommAlgCat.comp_apply, h]
  rfl

variable (B) in
/-- The triple tensor product as a test algebra. -/
abbrev cube : CommAlgCat.{u} R := CommAlgCat.of R ((B ⊗[R] B) ⊗[R] B)

variable (B) in
/-- The inclusion of the first factor of the triple tensor product. -/
def i₁ : B ⟶ cube B :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft)

variable (B) in
/-- The inclusion of the middle factor. -/
def i₂ : B ⟶ cube B :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeRight)

variable (B) in
/-- The inclusion of the last factor. -/
def i₃ : B ⟶ cube B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight

theorem pair_i₁_i₂ (w : B ⊗[R] B) : (pair (i₁ B) (i₂ B)).hom w = w ⊗ₜ[R] (1 : B) := by
  induction w with
  | tmul x y =>
    rw [pair_tmul]
    simp [i₁, i₂, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, TensorProduct.add_tmul]

theorem pair_i₂_i₃ (w : B ⊗[R] B) :
    (pair (i₂ B) (i₃ B)).hom w = (TensorProduct.assoc R B B B).symm ((1 : B) ⊗ₜ[R] w) := by
  induction w with
  | tmul x y =>
    rw [pair_tmul]
    simp [i₂, i₃, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, TensorProduct.tmul_add, map_add]

theorem i₁_mul_assoc_symm (p : B) (w : B ⊗[R] B) :
    ((p ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : B)) * (TensorProduct.assoc R B B B).symm ((1 : B) ⊗ₜ[R] w) =
      (TensorProduct.assoc R B B B).symm (p ⊗ₜ[R] w) := by
  induction w with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, mul_add, hx, hy, TensorProduct.tmul_add,
      map_add]

theorem coassoc : Comodule.Coassoc (comulL e) := by
  have hassoc := mul_assoc (pt e (i₁ B)) (pt e (i₂ B)) (pt e (i₃ B))
  rw [pt_mul, pt_mul, pt_mul, pt_mul] at hassoc
  have h := e.homEquiv.injective hassoc
  have hA : ∀ z : B ⊗[R] B, (pair (comul e ≫ pair (i₁ B) (i₂ B)) (i₃ B)).hom z =
      (comulL e).rTensor B z := by
    intro z
    induction z with
    | tmul p q =>
      rw [pair_tmul, CommAlgCat.hom_comp, AlgHom.comp_apply, pair_i₁_i₂]
      simp [i₃, Algebra.TensorProduct.tmul_mul_tmul, comulL_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hB : ∀ z : B ⊗[R] B, (pair (i₁ B) (comul e ≫ pair (i₂ B) (i₃ B))).hom z =
      (TensorProduct.assoc R B B B).symm ((comulL e).lTensor B z) := by
    intro z
    induction z with
    | tmul p q =>
      rw [pair_tmul, CommAlgCat.hom_comp, AlgHom.comp_apply, pair_i₂_i₃]
      simp only [i₁, CommAlgCat.hom_ofHom, AlgHom.comp_apply,
        Algebra.TensorProduct.includeLeft_apply, LinearMap.lTensor_tmul, comulL_apply]
      exact i₁_mul_assoc_symm p _
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun f : B ⟶ cube B => f.hom x) h
  simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at hx
  rw [← comulL_apply, hA, hB] at hx
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [hx, LinearEquiv.apply_symm_apply]

end Coalgebra

section Matrix

variable {n : Type} [Fintype n] [DecidableEq n] (a : Matrix n n B)
  (hmul : ∀ i j, comulL e (a i j) = ∑ l, a i l ⊗ₜ[R] a l j)
  (hone : ∀ i j, counitL e (a i j) = (1 : Matrix n n R) i j)

include hmul hone in
/-- The matrix of coefficients `a` evaluated at the classifying map of a point. -/
def coeffHom (S : CommAlgCat.{u} R) : F.obj S →* Matrix n n S where
  toFun x := (cls e x).hom.mapMatrix a
  map_one' := by
    rw [cls_one]
    ext i j
    have := hone i j
    rw [counitL_apply] at this
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, CommAlgCat.hom_comp, AlgHom.comp_apply,
      this, unitMap, CommAlgCat.hom_ofHom, Algebra.ofId_apply, Matrix.one_apply]
    split_ifs <;> simp
  map_mul' x y := by
    rw [cls_mul]
    ext i j
    have := hmul i j
    rw [comulL_apply] at this
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, CommAlgCat.hom_comp, AlgHom.comp_apply,
      this, map_sum, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => pair_tmul _ _ _ _

theorem coeffHom_apply (S : CommAlgCat.{u} R) (x : F.obj S) :
    coeffHom e a hmul hone S x = (cls e x).hom.mapMatrix a := rfl

/-- The natural homomorphism from `F` to the general linear group given by the coefficients. -/
def toGL : F ⟶ GeneralLinear.functor n R where
  app S := GrpCat.ofHom (coeffHom e a hmul hone S).toHomUnits
  naturality S T g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    ext i j
    change (cls e (F.map g x)).hom.mapMatrix a i j = g.hom ((cls e x).hom.mapMatrix a i j)
    rw [cls_map]
    rfl

/-- The coefficient homomorphism is a closed immersion once the coefficients span a set of
algebra generators. -/
theorem isClosedSubgroup_toGL (s : Set B) (hs : Algebra.adjoin R s = ⊤)
    (hspan : s ⊆ Submodule.span R (Set.range fun p : n × n => a p.1 p.2)) :
    IsClosedSubgroup
      (groupSchemeMap e (GeneralLinear.corepresentableBy n R) (toGL e a hmul hone)) := by
  unfold IsClosedSubgroup
  rw [groupSchemeMap_hom]
  apply IsClosedImmersion.spec_of_surjective
  set g : GL n B := (toGL e a hmul hone).app B (e.homEquiv (𝟙 B)) with hgdef
  have hg : ∀ i j, (g : Matrix n n B) i j = a i j := by
    intro i j
    change (cls e (pt e (𝟙 B))).hom.mapMatrix a i j = a i j
    rw [cls_pt]
    rfl
  let φ : GeneralLinear.CoordinateRing n R →ₐ[R] B := GeneralLinear.classify g
  have hmem : ∀ i j, a i j ∈ φ.range := by
    intro i j
    refine (AlgHom.mem_range φ).mpr
      ⟨GeneralLinear.quotient n R (MvPolynomial.X (GeneralLinear.Coordinate.entry i j)), ?_⟩
    change GeneralLinear.classify g _ = _
    rw [GeneralLinear.classify_entry, hg]
  have hspan' : Submodule.span R (Set.range fun p : n × n => a p.1 p.2) ≤
      Subalgebra.toSubmodule φ.range := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hmem p.1 p.2
  have hadj : Algebra.adjoin R s ≤ φ.range :=
    Algebra.adjoin_le fun x hx => hspan' (hspan hx)
  rw [hs, top_le_iff] at hadj
  exact (AlgHom.range_eq_top φ).mp hadj

end Matrix

end LinearEmbedding

open LinearEmbedding in
/-- Over a field, a corepresented group functor with finite type representing algebra has a
closed embedding into a general linear group. -/
theorem exists_isClosedSubgroup (k : Type u) [Field k]
    {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B : CommAlgCat.{u} (CommRingCat.of k)}
    (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    [Algebra.FiniteType (CommRingCat.of k) B] :
    ∃ (N : ℕ) (ρ : groupScheme F e ⟶ GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)),
      IsClosedSubgroup ρ := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := CommRingCat.of k) (A := B)
  obtain ⟨N, a, hmul, hone, hspan⟩ :=
    Comodule.exists_matrix (coassoc e) (leftCounit e) (rightCounit e) s
  exact ⟨N, groupSchemeMap e (GeneralLinear.corepresentableBy (Fin N) (CommRingCat.of k))
      (toGL e a hmul hone),
    isClosedSubgroup_toGL e a hmul hone (s : Set B) hs fun x hx => hspan x hx⟩

end Langlands.GroupScheme.Corepresented
