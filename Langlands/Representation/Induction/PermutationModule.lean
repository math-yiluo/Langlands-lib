import Langlands.Representation.Induction.OpenAdjunction

/-!
# Compact induction of trivial representations as permutation modules

For a group `G` acting on a set `X` and an `R`-module `M`, `permutation R G X M` is the
representation of `G` on finitely supported functions `X →₀ M` in which `g` moves the value at
`x` to `g • x`. With coefficients `R` it is Mathlib's `Representation.ofMulAction R G X` on the
monoid algebra `R[X]` (`permutationSelfEquiv`); with coefficients in the free module `I →₀ R` it
is the direct sum over `I` of copies of that representation (`permutationFinsuppEquiv`).

For an open subgroup `H` of a topological group `G`, the published compact induction
`compactInduced H (Representation.trivial R H M)` consists of the functions `f : G → M` that are
invariant under left translation by `H`, invariant under right translation by some open subgroup,
and compactly supported modulo `H`. `permutationEquiv` identifies it, as a representation of `G`,
with `permutation R G (G ⧸ H) M`: the function `f` goes to `y H ↦ f y⁻¹` (`toPermutation`), with
inverse `ofPermutation`. The permutation representation on `G ⧸ H` is smooth
(`isSmooth_permutation`), and the identification is natural in `M`:
`compactInductionTrivialNatIso` is a natural isomorphism from `Rep.trivialFunctor R H` followed by
`compactInductionFunctor H` to `permutationFunctor R H hH`.

For `H` normal, `R[G ⧸ H]` with the action of `G` is the left regular representation of `G ⧸ H`
pulled back along the quotient map (`ofMulAction_quotient`). Hence compact induction of the
trivial representation on `I →₀ R` is the free `R[G ⧸ H]`-module of rank `I`, as a
representation of `G` (`compactInducedFreeEquiv`); the coefficient ring `R` is arbitrary, for
example `𝒪/ℓ^m𝒪`.

Source: Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), proof of Proposition 4.10, printed pp.311-312: `C^j(ẽ)` "has been chosen to be
a direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules", and `C^j_m(ẽ)^{H_p}` and
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` "are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules". This module identifies
free modules over `R[G ⧸ H]`, for an open normal subgroup `H`, with compact inductions of trivial
representations. It does not prove that Harris's modules are free; the definitions and proofs
are ours.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uR uG uX uM uN uI

section Permutation

variable (R : Type uR) (G : Type uG) (X : Type uX) (M : Type uM) {N : Type uN}
variable [CommRing R] [Group G] [MulAction G X] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- The permutation representation of `G` on finitely supported `M`-valued functions on a
`G`-set `X`: the element `g` moves the value at `x` to `g • x`. -/
def permutation : Representation R G (X →₀ M) where
  toFun g := Finsupp.lmapDomain M R (g • ·)
  map_one' := by
    refine Finsupp.lhom_ext fun x m => ?_
    simp
  map_mul' g h := by
    refine Finsupp.lhom_ext fun x m => ?_
    simp [mul_smul]

variable {R G X M}

/-- The permutation action moves a single value at `x` to `g • x`. -/
@[simp] theorem permutation_single (g : G) (x : X) (m : M) :
    permutation R G X M g (Finsupp.single x m) = Finsupp.single (g • x) m :=
  Finsupp.mapDomain_single

/-- The value of `g • φ` at `x` is the value of `φ` at `g⁻¹ • x`. -/
theorem permutation_apply (g : G) (φ : X →₀ M) (x : X) :
    permutation R G X M g φ x = φ (g⁻¹ • x) := by
  have h := Finsupp.mapDomain_apply_of_injective (MulAction.injective g) φ (g⁻¹ • x)
  rw [smul_inv_smul] at h
  exact h

/-- Applying a linear map to the values commutes with the permutation action. -/
def permutationMap (f : M →ₗ[R] N) :
    (permutation R G X M).IntertwiningMap (permutation R G X N) where
  toLinearMap := Finsupp.mapRange.linearMap f
  isIntertwining' g := by
    refine Finsupp.lhom_ext fun x m => ?_
    simp

/-- `permutationMap f` applies `f` to each value. -/
theorem permutationMap_apply (f : M →ₗ[R] N) (φ : X →₀ M) (x : X) :
    permutationMap (G := G) f φ x = f (φ x) :=
  Finsupp.mapRange_apply (hf := map_zero f)

variable (R G X)

/-- With coefficients in `R`, the permutation representation is Mathlib's representation
`Representation.ofMulAction R G X` on the monoid algebra `R[X]`. -/
def permutationSelfEquiv :
    (permutation R G X R).Equiv (Representation.ofMulAction R G X) :=
  .mk (MonoidAlgebra.coeffLinearEquiv R).symm fun _ => LinearMap.ext fun _ => rfl

/-- With coefficients in the free module `I →₀ R`, the permutation representation is the direct
sum over `I` of copies of `Representation.ofMulAction R G X`. -/
def permutationFinsuppEquiv (I : Type uI) :
    (permutation R G X (I →₀ R)).Equiv ((Representation.ofMulAction R G X).finsupp I) :=
  .mk ((Finsupp.curryLinearEquiv R).symm ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm X I) ≪≫ₗ
      Finsupp.curryLinearEquiv R ≪≫ₗ
      Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv R).symm) fun g => by
    refine Finsupp.lhom_ext fun x m => ?_
    induction m using Finsupp.induction_linear with
    | zero => simp only [Finsupp.single_zero, map_zero]
    | add m n hm hn => rw [Finsupp.single_add, map_add, map_add, hm, hn]
    | single i r =>
      simp [Representation.finsupp_single, Finsupp.uncurry_single, Finsupp.curry_single]

end Permutation

section Smooth

variable {R : Type uR} {G : Type uG} {M : Type uM}
variable [CommRing R] [Group G] [AddCommGroup M] [Module R M]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- For an open subgroup `H`, the stabilizer `x H x⁻¹` of the coset `x H` is open. -/
theorem isOpen_stabilizer_mk (H : Subgroup G) (hH : IsOpen (H : Set G)) (x : G) :
    IsOpen (MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H) : Set G) := by
  have hc : Continuous fun y : G => x⁻¹ * y * x :=
    (continuous_const.mul continuous_id).mul continuous_const
  convert hH.preimage hc using 1
  ext y
  change (QuotientGroup.mk (y * x) : G ⧸ H) = QuotientGroup.mk x ↔ x⁻¹ * y * x ∈ H
  rw [eq_comm, QuotientGroup.eq, mul_assoc]

/-- For an open subgroup `H`, the stabilizer of the coset `x H`, as an open subgroup. -/
def cosetStabilizer (H : Subgroup G) (hH : IsOpen (H : Set G)) (x : G) : OpenSubgroup G :=
  ⟨MulAction.stabilizer G (QuotientGroup.mk x : G ⧸ H), isOpen_stabilizer_mk H hH x⟩

/-- For an open subgroup `H`, the permutation representation on `G ⧸ H` is smooth. -/
theorem isSmooth_permutation (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsSmooth (permutation R G (G ⧸ H) M) := by
  intro φ
  change φ ∈ smoothVectors (permutation R G (G ⧸ H) M)
  induction φ using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add φ ψ hφ hψ => exact Submodule.add_mem _ hφ hψ
  | single q m =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨cosetStabilizer H hH x, ?_⟩
    change ∀ k : (cosetStabilizer H hH x).toSubgroup,
      permutation R G (G ⧸ H) M (k : G) (Finsupp.single (QuotientGroup.mk x) m) =
        Finsupp.single (QuotientGroup.mk x) m
    intro k
    rw [permutation_single, MulAction.mem_stabilizer_iff.mp k.property]

end Smooth

section Induction

variable (R : Type uR) {G : Type uG} (M : Type uM)
variable [CommRing R] [Group G] [AddCommGroup M] [Module R M]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (hH : IsOpen (H : Set G))

variable {R M}

/-- The value at `y⁻¹` of a compactly induced function of a trivial representation, which
depends only on the coset `y H`. -/
def cosetValue (f : CompactFunctions H (Representation.trivial R H M)) (q : G ⧸ H) : M :=
  Quotient.liftOn' q (fun y => eval H _ f.1 y⁻¹) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h := f.1.1.property ⟨(a⁻¹ * b)⁻¹, H.inv_mem hab'⟩ a⁻¹
    have hx : H.subtype ⟨(a⁻¹ * b)⁻¹, H.inv_mem hab'⟩ * a⁻¹ = b⁻¹ := by
      simp [mul_inv_rev]
    rw [hx] at h
    exact h.symm)

/-- The value of `cosetValue H f` at the coset `y H` is the value of `f` at `y⁻¹`. -/
theorem cosetValue_mk (f : CompactFunctions H (Representation.trivial R H M)) (y : G) :
    cosetValue H f (QuotientGroup.mk y) = eval H _ f.1 y⁻¹ :=
  rfl

include hH in
/-- For `H` open, `cosetValue H f` has finite support: its support is the image of the support
of `f` modulo `H`, which is compact in a discrete space. -/
theorem cosetValue_support_finite (f : CompactFunctions H (Representation.trivial R H M)) :
    (Function.support (cosetValue H f)).Finite := by
  refine ((quotientSupport_finite H _ hH f).image
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)).subset ?_
  intro q hq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨quotientMap H y⁻¹, ⟨y⁻¹, hq, rfl⟩, ?_⟩
  change (QuotientGroup.mk y⁻¹⁻¹ : G ⧸ H) = QuotientGroup.mk y
  rw [inv_inv]

variable (R M)

/-- A compactly induced function of a trivial representation as a finitely supported
function on `G ⧸ H`: its value at `y H` is the value of the function at `y⁻¹`. -/
def toPermutation :
    CompactFunctions H (Representation.trivial R H M) →ₗ[R] (G ⧸ H →₀ M) where
  toFun f := Finsupp.ofSupportFinite (cosetValue H f) (cosetValue_support_finite H hH f)
  map_add' _ _ := Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl
  map_smul' _ _ := Finsupp.ext fun q => Quotient.inductionOn' q fun _ => rfl

variable {R M}

/-- The value of `toPermutation` at the coset `y H` is the value of the function at `y⁻¹`. -/
theorem toPermutation_mk (f : CompactFunctions H (Representation.trivial R H M)) (y : G) :
    toPermutation R M H hH f (QuotientGroup.mk y) = eval H _ f.1 y⁻¹ :=
  rfl

/-- The function `x ↦ φ (x⁻¹ H)` on `G` attached to a finitely supported function on `G ⧸ H`;
its uniform open stabilizer is one fixing `φ` under the permutation action. -/
def ofPermutation (φ : G ⧸ H →₀ M) : CompactFunctions H (Representation.trivial R H M) :=
  compactFunctionOf H (Representation.trivial R H M) (fun x => φ (QuotientGroup.mk x⁻¹))
    (by
      intro p x
      rw [Representation.trivial_apply]
      exact congrArg φ (QuotientGroup.eq.mpr (by simp)))
    (isSmooth_permutation (R := R) H hH φ).choose
    (by
      intro k x
      have hk : permutation R G (G ⧸ H) M (k : G) φ = φ :=
        (isSmooth_permutation (R := R) H hH φ).choose_spec k
      calc φ (QuotientGroup.mk (x * (k : G))⁻¹)
          = permutation R G (G ⧸ H) M (k : G) φ (QuotientGroup.mk x⁻¹) := by
            rw [permutation_apply, MulAction.Quotient.smul_mk, mul_inv_rev, smul_eq_mul]
        _ = φ (QuotientGroup.mk x⁻¹) := by rw [hk])
    (by
      refine ((φ.support.finite_toSet.image
        (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm).subset ?_).isCompact
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨QuotientGroup.mk x⁻¹, Finsupp.mem_support_iff.mpr hx, ?_⟩
      change quotientMap H x⁻¹⁻¹ = quotientMap H x
      rw [inv_inv])

/-- The function `ofPermutation H hH φ` takes the value `φ (x⁻¹ H)` at `x`. -/
theorem eval_ofPermutation (φ : G ⧸ H →₀ M) (x : G) :
    eval H _ (ofPermutation (R := R) H hH φ).1 x = φ (QuotientGroup.mk x⁻¹) :=
  rfl

variable (R M)

/-- Compactly induced functions of the trivial representation on `M` are the finitely
supported `M`-valued functions on `G ⧸ H`. -/
def permutationLinearEquiv :
    CompactFunctions H (Representation.trivial R H M) ≃ₗ[R] (G ⧸ H →₀ M) where
  __ := toPermutation R M H hH
  invFun := ofPermutation (R := R) H hH
  left_inv f := compactFunctions_ext H _ fun x => by
    change eval H _ f.1 x⁻¹⁻¹ = eval H _ f.1 x
    rw [inv_inv]
  right_inv φ := Finsupp.ext fun q => Quotient.inductionOn' q fun y => by
    change φ (QuotientGroup.mk y⁻¹⁻¹) = φ (QuotientGroup.mk y)
    rw [inv_inv]

/-- Compact induction of the trivial representation on `M` from an open subgroup `H` is the
permutation representation on finitely supported `M`-valued functions on `G ⧸ H`. -/
def permutationEquiv :
    (compactInduced H (Representation.trivial R H M)).Equiv (permutation R G (G ⧸ H) M) :=
  .mk (permutationLinearEquiv R M H hH) fun g => LinearMap.ext fun f =>
    Finsupp.ext fun q => Quotient.inductionOn' q fun y => by
      change eval H _ f.1 (y⁻¹ * g) =
        permutation R G (G ⧸ H) M g (toPermutation R M H hH f) (QuotientGroup.mk y)
      rw [permutation_apply, MulAction.Quotient.smul_mk, smul_eq_mul, toPermutation_mk,
        mul_inv_rev, inv_inv]

/-- The smooth permutation representation on finitely supported `M`-valued functions on `G ⧸ H`. -/
abbrev smoothPermutation : Langlands.SmoothRep.{uR, uG, max uG uM} R G :=
  SmoothRep.of (permutation R G (G ⧸ H) M) (isSmooth_permutation H hH)

/-- Compact induction of the trivial representation on `M`, as an isomorphism of smooth
representations with the permutation representation on `G ⧸ H`. -/
def compactInductionTrivialIso :
    (compactInductionFunctor H).obj (Rep.trivial R H M) ≅ smoothPermutation R M H hH :=
  SmoothRep.mkIso (permutationEquiv R M H hH)

end Induction

section Functor

variable (R : Type uR) {G : Type uG}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- The smooth permutation representation on `G ⧸ H`, as a functor of the coefficient module. -/
def permutationFunctor : ModuleCat.{uM} R ⥤ SmoothRep.{uR, uG, max uG uM} R G where
  obj M := smoothPermutation R M H hH
  map f := SmoothRep.ofHom (permutationMap (G := G) (X := G ⧸ H) f.hom)
  map_id _ := by ext φ q; rfl
  map_comp _ _ := by ext φ q; rfl

/-- Compact induction from an open subgroup `H` of trivial representations is naturally
isomorphic to the permutation functor on `G ⧸ H`. -/
def compactInductionTrivialNatIso :
    (Rep.trivialFunctor R H : ModuleCat.{uM} R ⥤ Rep.{uM} R H) ⋙ compactInductionFunctor H ≅
      permutationFunctor R H hH :=
  NatIso.ofComponents (fun M => compactInductionTrivialIso R M H hH) fun _ => by
    ext φ
    refine Finsupp.ext fun q => ?_
    induction q using QuotientGroup.induction_on
    rfl

end Functor

section Normal

variable (R : Type uR) {G : Type uG} [CommRing R] [Group G] (H : Subgroup G) [H.Normal]

/-- For a normal subgroup `H`, the representation of `G` on `R[G ⧸ H]` is the left regular
representation of `G ⧸ H` pulled back along the quotient map. -/
theorem ofMulAction_quotient :
    Representation.ofMulAction R G (G ⧸ H) =
      (Representation.leftRegular R (G ⧸ H)).comp (QuotientGroup.mk' H) := by
  refine MonoidHom.ext fun g => ?_
  have h : (fun q : G ⧸ H => g • q) = fun q => QuotientGroup.mk' H g • q :=
    funext fun q => QuotientGroup.induction_on q fun _ => rfl
  rw [MonoidHom.comp_apply, Representation.ofMulAction_def, Representation.ofMulAction_def, h]

/-- For a normal subgroup `H`, the direct sum over `I` of copies of `R[G ⧸ H]` is the free
`R[G ⧸ H]`-module of rank `I`, pulled back along the quotient map. -/
theorem finsupp_ofMulAction_quotient (I : Type uI) :
    (Representation.ofMulAction R G (G ⧸ H)).finsupp I =
      (Representation.free R (G ⧸ H) I).comp (QuotientGroup.mk' H) := by
  rw [ofMulAction_quotient]
  rfl

end Normal

section NormalInduction

variable (R : Type uR) {G : Type uG}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) [H.Normal] (hH : IsOpen (H : Set G))

/-- For an open normal subgroup `H`, compact induction of the trivial representation on the free
module `I →₀ R` is the free `R[G ⧸ H]`-module of rank `I`, as a representation of `G`. -/
def compactInducedFreeEquiv (I : Type uI) :
    (compactInduced H (Representation.trivial R H (I →₀ R))).Equiv
      ((Representation.free R (G ⧸ H) I).comp (QuotientGroup.mk' H)) :=
  let e := (permutationEquiv R (I →₀ R) H hH).trans (permutationFinsuppEquiv R G (G ⧸ H) I)
  .mk e.toLinearEquiv fun g => by
    rw [← finsupp_ofMulAction_quotient]
    exact e.toIntertwiningMap.isIntertwining' g

end NormalInduction

end Langlands.Induction
