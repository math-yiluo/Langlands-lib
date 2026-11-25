/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ResidueSequenceKummer
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ResidueSequenceRestrict

/-!
# The Gysin map and exactness of the residue sequence at the boundary

Let `C` be a smooth proper connected curve over an algebraically closed field `k`, `U ⊆ C` a
nonempty open with boundary `D = C ∖ U`, and `N` invertible in `k`. The residue sequence (5.1)
of blueprint `proposition-no-fixed-class-degree-one--1`

`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → H⁰(D, ℤ / N (-1)) → H²(C, ℤ / N)`

has as last map the Gysin map (`AlgebraicGeometry.Scheme.gysinH2`): a family
`a = (a_z)_{z ∈ D}` of homomorphisms `a_z : μ_N(k) → ℤ / N` is sent to `∑_z H²(a_z)(c₁(𝒪(z)))`,
where `c₁ : Pic(C) → H²(C, μ_N)` is the Kummer map
(`AlgebraicGeometry.Scheme.picToSheafHTwo`) and `H²(a_z)` is induced by the map of étale sheaves
`μ_N → ℤ / N` given by `a_z` (`AlgebraicGeometry.Scheme.rootsOfUnitySheafHom`).

The sequence is exact at `H⁰(D, ℤ / N (-1))`
(`AlgebraicGeometry.Scheme.range_residueH1_eq_ker_gysinH2`). Via the trace
`H²(C, μ_N) ≅ ℤ / N` (degree modulo `N`), the kernel of the Gysin map consists of the families
with `∑_z a_z(ζ) = 0` for a primitive root of unity `ζ`
(`AlgebraicGeometry.Scheme.gysinH2_eq_zero_iff`). If `x ^ N = f` is a Kummer element of a
torsor on `U`, its residue at `z` is `ord_z f mod N`; this vanishes at the closed points of `U`
and `∑_z ord_z f = deg div f = 0`, so residues lie in the kernel. Conversely if
`∑_z a_z(ζ) = 0`, the divisor `E = ∑_z a_z(ζ) [z]` has degree divisible by `N`; as `Pic⁰(C)`
is divisible, `E = N E' + div f`, and the Kummer torsor of `f`, defined on the open where `f` is
a unit, extends to `U` and has residues `a`.

The whole sequence is `AlgebraicGeometry.Scheme.residueSequence_exact`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- On an element killed by `N`, the multiples by the representatives of `ZMod N` are additive. -/
lemma ZMod.val_add_nsmul {A : Type*} [AddMonoid A] {N : ℕ} [NeZero N] {t : A} (ht : N • t = 0)
    (x y : ZMod N) : (x + y).val • t = x.val • t + y.val • t := by
  rw [ZMod.val_add, ← add_nsmul]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) N, add_nsmul, mul_nsmul, ht,
    nsmul_zero, add_zero]

namespace AlgebraicGeometry.Scheme

/-- Homomorphisms out of `μ_N(k)` agree if they agree on a primitive `N`-th root of unity. -/
lemma addMonoidHom_ext_rootsOfUnity {k : Type u} [Field k] {N : ℕ} [NeZero N] {A : Type*}
    [AddCommGroup A] {ζ : k} (hζ : IsPrimitiveRoot ζ N)
    {φ ψ : Additive (rootsOfUnity N k) →+ A}
    (h : φ (Additive.ofMul hζ.toRootsOfUnity) = ψ (Additive.ofMul hζ.toRootsOfUnity)) :
    φ = ψ := by
  refine AddMonoidHom.ext fun ξ ↦ ?_
  have hξ : ((ξ.toMul : kˣ) : k) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N _).1 ξ.toMul.2, Units.val_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have hξi : ξ = i • Additive.ofMul hζ.toRootsOfUnity := by
    apply Additive.toMul.injective
    ext
    simp [← hi]
  rw [hξi, map_nsmul, map_nsmul, h]

section Trivialization

variable {X : Scheme.{u}} (n : ℕ)

/-- On the constant sheaf `ℤ / n`, multiplication by `n` vanishes. -/
lemma nsmul_id_constantZMod : n • 𝟙 (X.constantZMod n) = 0 := by
  have h : n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) = 0 := by
    ext x
    simp [nsmul_eq_mul]
  rw [← (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_id, ← Functor.map_nsmul,
    h, Functor.map_zero]

lemma zmodToGmPresheaf_pow [NeZero n] (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (b : ℕ) :
    X.zmodToGmPresheaf n (ζ ^ b) (by rw [pow_right_comm, hζ, one_pow]) =
      b • X.zmodToGmPresheaf n ζ hζ := by
  ext U ⟨a⟩
  rw [← ZMod.natCast_zmod_val a]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  have e2 (c : ℕ) (y : X.gmPresheaf.obj U) :
      ((Additive.toMul (c • y).down : Γ(U.unop.left, ⊤)ˣ) : Γ(U.unop.left, ⊤)) =
        ((Additive.toMul y.down : Γ(U.unop.left, ⊤)ˣ) : Γ(U.unop.left, ⊤)) ^ c := by
    induction c with
    | zero => rfl
    | succ c ih => rw [succ_nsmul, pow_succ, ← ih]; rfl
  refine (X.zmodToGmPresheaf_app_natCast n (ζ ^ b) _ U a.val).trans ?_
  have h := X.zmodToGmPresheaf_app_natCast n ζ hζ U a.val
  have e : ((b • X.zmodToGmPresheaf n ζ hζ).app U) (ULift.up (a.val : ZMod n)) =
      b • (X.zmodToGmPresheaf n ζ hζ).app U (ULift.up (a.val : ZMod n)) := by
    rw [NatTrans.app_nsmul]
    rfl
  rw [e]
  refine Eq.trans ?_ (e2 b _).symm
  rw [h, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, ← pow_mul, mul_comm]
/-- `θ_{ζ ^ b} = θ_ζ ∘ b` for the maps `θ_ζ : ℤ / n ⟶ 𝔾ₘ`, `c ↦ ζ ^ c`. -/
lemma constantZModToGmSheaf_pow [NeZero n] (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (b : ℕ) :
    X.constantZModToGmSheaf n (ζ ^ b) (by rw [pow_right_comm, hζ, one_pow]) =
      (b • 𝟙 _) ≫ X.constantZModToGmSheaf n ζ hζ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ X.isSheaf_gmPresheaf
  have e : (b • 𝟙 (X.constantZMod n)).hom = b • 𝟙 _ :=
    (sheafToPresheaf _ _).map_nsmul (f := 𝟙 (X.constantZMod n)) (n := b)
  rw [InducedCategory.comp_hom, toSheafify_constantZModToGmSheaf, zmodToGmPresheaf_pow n ζ hζ b,
    e, Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    toSheafify_constantZModToGmSheaf]

/-- `θ_{ζ ^ b} = θ_ζ ∘ b` for the maps `θ_ζ : ℤ / n ⟶ μ_n`, `c ↦ ζ ^ c`. -/
lemma constantZModToRootsOfUnitySheaf_pow [NeZero n] (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (b : ℕ) :
    X.constantZModToRootsOfUnitySheaf n (ζ ^ b) (by rw [pow_right_comm, hζ, one_pow]) =
      (b • 𝟙 _) ≫ X.constantZModToRootsOfUnitySheaf n ζ hζ := by
  rw [← cancel_mono (kernel.ι (n • 𝟙 X.gmSheaf))]
  simp only [constantZModToRootsOfUnitySheaf, Category.assoc, kernel.lift_ι]
  exact constantZModToGmSheaf_pow n ζ hζ b

lemma constantZModToRootsOfUnitySheaf_congr {ζ ζ' : Γ(X, ⊤)ˣ} (h : ζ = ζ') (hζ : ζ ^ n = 1)
    (hζ' : ζ' ^ n = 1) :
    X.constantZModToRootsOfUnitySheaf n ζ hζ = X.constantZModToRootsOfUnitySheaf n ζ' hζ' := by
  subst h
  rfl

/-- `θ_{ζ ^ b} = θ_ζ ∘ b` for the trivializations `θ_ζ : ℤ / n ≅ μ_n` of primitive roots of
unity of the base field. -/
lemma constantZModIsoRootsOfUnitySheaf_pow_hom {k : Type u} [Field k] [NeZero n]
    (f : X ⟶ Spec (.of k)) {ζ : k} (hζ : IsPrimitiveRoot ζ n) (b : ℕ)
    (hζb : IsPrimitiveRoot (ζ ^ b) n) :
    (X.constantZModIsoRootsOfUnitySheaf n f hζb).hom =
      (b • 𝟙 _) ≫ (X.constantZModIsoRootsOfUnitySheaf n f hζ).hom := by
  simp only [constantZModIsoRootsOfUnitySheaf, asIso_hom]
  rw [← constantZModToRootsOfUnitySheaf_pow]
  exact constantZModToRootsOfUnitySheaf_congr n (Units.ext (by simp [map_pow])) _ _

end Trivialization

section RootsOfUnityHom

variable (k : Type u) [Field k] (N : ℕ) [NeZero N] [NeZero (N : k)]

/-- A chosen primitive `N`-th root of unity of `k`, for `k` with enough roots of unity. -/
noncomputable def primitiveRootOfUnity [HasEnoughRootsOfUnity k N] : k :=
  (HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N).choose

omit [NeZero N] [NeZero (N : k)] in
lemma isPrimitiveRoot_primitiveRootOfUnity [HasEnoughRootsOfUnity k N] :
    IsPrimitiveRoot (primitiveRootOfUnity k N) N :=
  (HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N).choose_spec

variable {k} [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The map of étale sheaves `μ_N → ℤ / N` induced by a homomorphism `a : μ_N(k) → ℤ / N`:
under the trivialization `θ_ζ : ℤ / N ≅ μ_N`, `c ↦ ζ ^ c`, of a primitive `N`-th root of unity
`ζ`, it is multiplication by `a(ζ)`. It is defined with a chosen `ζ`, but does not depend on it
(`AlgebraicGeometry.Scheme.rootsOfUnitySheafHom_eq`). -/
noncomputable def rootsOfUnitySheafHom (a : Additive (rootsOfUnity N k) →+ ZMod N) :
    X.rootsOfUnitySheaf N ⟶ X.constantZMod N :=
  (X.constantZModIsoRootsOfUnitySheaf N (X ↘ Spec (.of k))
      (isPrimitiveRoot_primitiveRootOfUnity k N)).inv ≫
    ((a (Additive.ofMul (isPrimitiveRoot_primitiveRootOfUnity k N).toRootsOfUnity)).val • 𝟙 _)

/-- On cohomology, the map induced by `a` is multiplication by `a(ζ)` after `θ_ζ⁻¹`. -/
lemma sheafHMap_rootsOfUnitySheafHom (a : Additive (rootsOfUnity N k) →+ ZMod N) {n : ℕ}
    (x : Sheaf.H (X.rootsOfUnitySheaf N) n) :
    Sheaf.H.map (X.rootsOfUnitySheafHom N a) n x =
      (a (Additive.ofMul (isPrimitiveRoot_primitiveRootOfUnity k N).toRootsOfUnity)).val •
        Sheaf.H.map (X.constantZModIsoRootsOfUnitySheaf N (X ↘ Spec (.of k))
          (isPrimitiveRoot_primitiveRootOfUnity k N)).inv n x := by
  rw [rootsOfUnitySheafHom, Sheaf.H.map_comp_apply, Sheaf.H.map_nsmul_apply,
    Sheaf.H.map_id_apply]

/-- The map `μ_N → ℤ / N` induced by `a` does not depend on the chosen primitive root of unity:
for every primitive `N`-th root of unity `ζ` of `k` it is the inverse of the trivialization
`θ_ζ : ℤ / N ≅ μ_N`, `c ↦ ζ ^ c`, followed by multiplication by `a(ζ)`. -/
theorem rootsOfUnitySheafHom_eq (a : Additive (rootsOfUnity N k) →+ ZMod N) {ζ : k}
    (hζ : IsPrimitiveRoot ζ N) :
    X.rootsOfUnitySheafHom N a =
      (X.constantZModIsoRootsOfUnitySheaf N (X ↘ Spec (.of k)) hζ).inv ≫
        ((a (Additive.ofMul hζ.toRootsOfUnity)).val • 𝟙 _) := by
  have hζ₀ := isPrimitiveRoot_primitiveRootOfUnity k N
  obtain ⟨b, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ.pow_eq_one
  set x := a (Additive.ofMul hζ₀.toRootsOfUnity)
  have ha : a (Additive.ofMul hζ.toRootsOfUnity) = ((b * x.val : ℕ) : ZMod N) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, ← map_nsmul]
    congr 1
    apply Additive.toMul.injective
    ext
    simp
  have key (m : ℕ) : ((m : ZMod N)).val • 𝟙 (X.constantZMod N) = m • 𝟙 _ := by
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div m N, add_nsmul, mul_nsmul, nsmul_id_constantZMod,
      nsmul_zero, add_zero]
  rw [rootsOfUnitySheafHom,
    ← cancel_epi (X.constantZModIsoRootsOfUnitySheaf N (X ↘ Spec (.of k)) hζ).hom,
    Iso.hom_inv_id_assoc, constantZModIsoRootsOfUnitySheaf_pow_hom N _ hζ₀ b hζ, Category.assoc,
    Iso.hom_inv_id_assoc, Preadditive.nsmul_comp, Category.id_comp, smul_smul, ha, key]

/-- The trivialization `θ_ζ` induces an injection on cohomology. -/
lemma injective_sheafHMap_constantZModIsoRootsOfUnitySheaf_inv (n : ℕ) :
    Function.Injective (Sheaf.H.map (X.constantZModIsoRootsOfUnitySheaf N (X ↘ Spec (.of k))
      (isPrimitiveRoot_primitiveRootOfUnity k N)).inv n) := fun x y h ↦ by
  have hx := Sheaf.H.map_comp_apply (X.constantZModIsoRootsOfUnitySheaf N (X ↘ Spec (.of k))
      (isPrimitiveRoot_primitiveRootOfUnity k N)).inv
    (X.constantZModIsoRootsOfUnitySheaf N (X ↘ Spec (.of k))
      (isPrimitiveRoot_primitiveRootOfUnity k N)).hom (n := n)
  rw [Iso.inv_hom_id] at hx
  rw [← Sheaf.H.map_id_apply x, ← Sheaf.H.map_id_apply y, hx, hx, h]

end RootsOfUnityHom

section Torsion

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The Kummer classes in `H²(X, μ_N)`, and their images under maps of sheaves, are killed
by `N`. -/
lemma nsmul_sheafHMap_picToSheafHTwo {N : ℕ} (hN : (N : k) ≠ 0) {F : Sheaf _ _}
    (φ : X.rootsOfUnitySheaf N ⟶ F) (L : Additive X.Pic) :
    N • Sheaf.H.map φ 2 (picToSheafHTwo N hN L) = 0 := by
  rw [← map_nsmul, ← map_nsmul, (picToSheafHTwo_eq_zero_iff N hN _).2 ⟨L, natCast_zsmul _ _⟩,
    map_zero]

end Torsion

section Gysin

open WeilGroup EtaleTorsor

variable {k : Type u} [Field k] {C U : Scheme.{u}} [C.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))] [IsIntegral C]
  (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]

variable (k) in
include k in
/-- The boundary points of a nonempty open of a smooth integral curve are closed. -/
lemma isClosed_singleton_of_notMem_range {z : C} (hz : z ∉ Set.range j.base) :
    IsClosed ({z} : Set C) := by
  have : IsCurve (C ↘ Spec (.of k)) := inferInstance
  have : Smooth (C ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have := irreducibleSpace_of_smooth (p := C ↘ Spec (.of k))
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  exact j.isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
    (IsCurve.krullDim_le_one (f := C ↘ Spec (.of k))) ⟨_, u, rfl⟩ hz

variable (k) in
include k in
/-- The boundary of a nonempty open of a smooth integral curve is finite. -/
lemma finite_compl_range : (Set.range j.base)ᶜ.Finite := by
  have : IsCurve (C ↘ Spec (.of k)) := inferInstance
  have : Smooth (C ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  exact finite_boundary (p := C ↘ Spec (.of k)) j

variable (k) in
/-- The boundary of a nonempty open of a smooth integral curve, as a finite type. -/
@[instance_reducible]
noncomputable def fintypeBoundary : Fintype ↥(Set.range j.base)ᶜ :=
  (finite_compl_range k j).fintype

variable (k) in
/-- A boundary point, as a closed point. -/
noncomputable def boundaryClosedPoint (z : ↥(Set.range j.base)ᶜ) : closedPoints C :=
  ⟨z.1, isClosed_singleton_of_notMem_range k j z.2⟩

lemma boundaryClosedPoint_injective : Function.Injective (boundaryClosedPoint k j) :=
  fun _ _ h ↦ Subtype.ext (congrArg Subtype.val h :)

variable (k) in
/-- The divisor `∑_{z ∈ D} c_z [z]` supported on the boundary. -/
noncomputable def boundaryDivisor (c : ↥(Set.range j.base)ᶜ → ℤ) : C.Divisor :=
  letI := fintypeBoundary k j
  ∑ z, Finsupp.single (boundaryClosedPoint k j z) (c z)

lemma boundaryDivisor_apply_boundaryClosedPoint (c : ↥(Set.range j.base)ᶜ → ℤ)
    (z : ↥(Set.range j.base)ᶜ) : boundaryDivisor k j c (boundaryClosedPoint k j z) = c z := by
  classical
  rw [boundaryDivisor, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, (boundaryClosedPoint_injective j).eq_iff]
  simp

lemma boundaryDivisor_apply_of_mem_range (c : ↥(Set.range j.base)ᶜ → ℤ) (P : closedPoints C)
    (hP : P.1 ∈ Set.range j.base) : boundaryDivisor k j c P = 0 := by
  classical
  rw [boundaryDivisor, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun z _ ↦ Finsupp.single_eq_of_ne ?_
  rintro rfl
  exact z.2 hP

lemma degree_boundaryDivisor (c : ↥(Set.range j.base)ᶜ → ℤ) :
    Divisor.degree C (boundaryDivisor k j c) = letI := fintypeBoundary k j; ∑ z, c z := by
  rw [boundaryDivisor, map_sum]
  simp

lemma toPic_boundaryDivisor (c : ↥(Set.range j.base)ᶜ → ℤ) :
    Divisor.toPic k C (boundaryDivisor k j c) = letI := fintypeBoundary k j;
      ∑ z, c z • Additive.ofMul (Pic.ofClosedPoint k (boundaryClosedPoint k j z)) := by
  rw [boundaryDivisor, map_sum]
  simp

variable [IsAlgClosed k]

variable (k) in
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the **Gysin map**
`H⁰(D, ℤ / N (-1)) → H²(C, ℤ / N)` of the residue sequence (5.1). A family `(a_z)_{z ∈ D}` of
homomorphisms `a_z : μ_N(k) → ℤ / N` indexed by the boundary `D = C ∖ U` is sent to
`∑_z H²(a_z)(c₁(𝒪(z)))`, where `c₁ : Pic(C) → H²(C, μ_N)` is the Kummer map and `H²(a_z)` is
induced by the map of sheaves `μ_N → ℤ / N` given by `a_z`
(`AlgebraicGeometry.Scheme.rootsOfUnitySheafHom`). -/
noncomputable def gysinH2 (N : ℕ) [NeZero N] [NeZero (N : k)] :
    ((z : ↥(Set.range j.base)ᶜ) → Additive (rootsOfUnity N k) →+ ZMod N) →+
      Sheaf.H (C.constantZMod N) 2 :=
  letI := fintypeBoundary k j
  { toFun a := ∑ z, Sheaf.H.map (C.rootsOfUnitySheafHom N (a z)) 2
        (picToSheafHTwo N (NeZero.ne (N : k))
          (.ofMul (Pic.ofClosedPoint k (boundaryClosedPoint k j z))))
    map_zero' := by
      refine Finset.sum_eq_zero fun z _ ↦ ?_
      rw [sheafHMap_rootsOfUnitySheafHom]
      simp
    map_add' a b := by
      refine (Finset.sum_congr rfl fun z _ ↦ ?_).trans Finset.sum_add_distrib
      simp only [sheafHMap_rootsOfUnitySheafHom, Pi.add_apply, AddMonoidHom.add_apply]
      exact ZMod.val_add_nsmul (nsmul_sheafHMap_picToSheafHTwo _ _ _) _ _ }

/-- The Gysin map is the image of the Kummer class of the divisor `∑_z a_z(ζ) [z]` under the
trivialization `θ_ζ : ℤ / N ≅ μ_N` of the chosen primitive root of unity `ζ`. -/
lemma gysinH2_apply (N : ℕ) [NeZero N] [NeZero (N : k)]
    (a : (z : ↥(Set.range j.base)ᶜ) → Additive (rootsOfUnity N k) →+ ZMod N) :
    gysinH2 k j N a = Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf N (C ↘ Spec (.of k))
      (isPrimitiveRoot_primitiveRootOfUnity k N)).inv 2 (picToSheafHTwo N (NeZero.ne (N : k))
        (Divisor.toPic k C (boundaryDivisor k j fun z ↦
          ((a z (Additive.ofMul (isPrimitiveRoot_primitiveRootOfUnity k N).toRootsOfUnity)).val :
            ℤ)))) := by
  rw [toPic_boundaryDivisor, map_sum, map_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [sheafHMap_rootsOfUnitySheafHom, map_zsmul, map_zsmul, natCast_zsmul]

variable [GeometricallyIntegral (C ↘ Spec (.of k))]

omit [GeometricallyIntegral (C ↘ Spec (.of k))] in
/-- The degree modulo `N` of the boundary divisor of a family `a`. -/
lemma picDegreeMod_toPic_boundaryDivisor (N : ℕ) [NeZero N]
    (c : ↥(Set.range j.base)ᶜ → ℤ) :
    picDegreeMod (k := k) N (Divisor.toPic k C (boundaryDivisor k j c)) =
      letI := fintypeBoundary k j; ∑ z, (c z : ZMod N) := by
  change ((picDegreeHom k C (Divisor.toPic k C _).toMul).toAdd : ZMod N) = _
  rw [picDegreeHom_toPic, toAdd_ofAdd, degree_boundaryDivisor, Int.cast_sum]

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the kernel of the Gysin map consists of
the families `(a_z)_{z ∈ D}` whose values at a primitive `N`-th root of unity sum to zero. -/
theorem gysinH2_eq_zero_iff (N : ℕ) [NeZero N] [NeZero (N : k)]
    (a : (z : ↥(Set.range j.base)ᶜ) → Additive (rootsOfUnity N k) →+ ZMod N) :
    gysinH2 k j N a = 0 ↔ letI := fintypeBoundary k j;
      ∑ z, a z (Additive.ofMul (isPrimitiveRoot_primitiveRootOfUnity k N).toRootsOfUnity) = 0 := by
  have hN : (N : k) ≠ 0 := NeZero.ne _
  have : Nonempty C := ⟨j (Classical.arbitrary U)⟩
  set c : ↥(Set.range j.base)ᶜ → ℤ := fun z ↦
    ((a z (Additive.ofMul (isPrimitiveRoot_primitiveRootOfUnity k N).toRootsOfUnity)).val : ℤ)
  have hsum : (letI := fintypeBoundary k j; ∑ z, (c z : ZMod N)) =
      letI := fintypeBoundary k j;
        ∑ z, a z (Additive.ofMul (isPrimitiveRoot_primitiveRootOfUnity k N).toRootsOfUnity) := by
    simp [c]
  rw [gysinH2_apply, ← hsum, ← picDegreeMod_toPic_boundaryDivisor j N c]
  rw [← map_zero (Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf N (C ↘ Spec (.of k))
      (isPrimitiveRoot_primitiveRootOfUnity k N)).inv 2),
    (injective_sheafHMap_constantZModIsoRootsOfUnitySheaf_inv N C 2).eq_iff]
  constructor
  · exact fun h ↦ ker_picToSheafHTwo_le N hN h
  · intro h
    have h' : Divisor.toPic k C (boundaryDivisor k j c) ∈ (picDegreeMod (k := k) (X := C) N).ker :=
      h
    rw [ker_picDegreeMod N (Nat.pos_of_ne_zero (NeZero.ne N))] at h'
    obtain ⟨L, hL⟩ := h'
    exact (picToSheafHTwo_eq_zero_iff N hN _).2 ⟨L, hL⟩

variable [IsLocallyNoetherian C] [ConnectedSpace U]

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: exactness of the residue sequence (5.1)

`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → H⁰(D, ℤ / N (-1)) → H²(C, ℤ / N)`

at `H⁰(D, ℤ / N (-1)) = ⊕_{z ∈ D} Hom(μ_N(k), ℤ / N)`: the image of the residue map is the
kernel of the Gysin map. Here `C` is a smooth proper connected curve over an algebraically
closed field `k`, `U ⊆ C` a nonempty open with boundary `D` and `N` invertible in `k`. -/
theorem range_residueH1_eq_ker_gysinH2 (N : ℕ) [NeZero N] [NeZero (N : k)] :
    (residueH1 j (C ↘ Spec (.of k)) N).range = (gysinH2 k j N).ker := by
  classical
  set p := C ↘ Spec (.of k)
  have : IsCurve (C ↘ Spec (.of k)) := inferInstance
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have := irreducibleSpace_of_smooth (p := p)
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian C := {}
  have hN : (N : k) ≠ 0 := NeZero.ne _
  set ζ := primitiveRootOfUnity k N
  have hζ : IsPrimitiveRoot ζ N := isPrimitiveRoot_primitiveRootOfUnity k N
  set ξ : Additive (rootsOfUnity N k) := Additive.ofMul hζ.toRootsOfUnity
  have hξ : ((ξ.toMul : kˣ) : k) = ζ := hζ.val_toRootsOfUnity_coe
  let := fintypeBoundary k j
  ext a
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, gysinH2_eq_zero_iff]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨T, rfl⟩ := (bijective_classH1 (M := ULift.{u + 1} (ZMod N)) (Y := U)).2 x
    induction T using Quotient.inductionOn with | h T => ?_
    simp only [residueH1_classH1]
    -- a Kummer element `x ^ N = f` of `T`
    obtain ⟨x, f, hx0, hf, hχ⟩ := T.exists_kummerElement j p hζ.pow_eq_one
    have hres (z : C) : T.residue j p z ξ = (C.ord f z : ZMod N) :=
      T.residue_eq_ord j p z ξ hx0 hf fun σ ↦ by rw [hξ]; exact hχ σ
    have hf0 : f ≠ 0 := ne_zero_of_algebraMap_eq_pow hx0 hf
    -- `div f` is divisible by `N` away from the boundary
    set F : Additive C.functionFieldˣ := .ofMul (Units.mk0 f hf0)
    set E := boundaryDivisor k j fun z ↦ C.ord f z.1
    have hdvd (P : closedPoints C) : (N : ℤ) ∣ (C.div F - E) P := by
      rw [Finsupp.sub_apply, div_apply]
      by_cases hP : P.1 ∈ Set.range j.base
      · rw [boundaryDivisor_apply_of_mem_range j _ P hP, sub_zero]
        have h := hres P.1
        rw [residue_eq_zero_of_mem_range T hP P.2, AddMonoidHom.zero_apply, eq_comm,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at h
        exact h
      · have h := boundaryDivisor_apply_boundaryClosedPoint (k := k) j
          (fun z ↦ C.ord f z.1) ⟨P.1, hP⟩
        rw [show E P = C.ord f P.1 from h]
        change (N : ℤ) ∣ C.ord f P.1 - C.ord f P.1
        rw [sub_self]
        exact dvd_zero _
    have hdeg : (N : ℤ) ∣ Divisor.degree C (C.div F - E) := by
      rw [Divisor.degree_apply]
      exact Finset.dvd_sum fun P _ ↦ hdvd P
    rw [map_sub, degree_div_eq_zero k, zero_sub, dvd_neg, degree_boundaryDivisor,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum] at hdeg
    rw [← hdeg]
    exact Finset.sum_congr rfl fun z _ ↦ hres z.1
  · intro ha
    -- the divisor `E = ∑_z a_z(ζ) [z]` has degree divisible by `N`
    set c : ↥(Set.range j.base)ᶜ → ℤ := fun z ↦ ((a z ξ).val : ℤ)
    set E := boundaryDivisor k j c
    have hE : picDegreeMod (k := k) N (Divisor.toPic k C E) = 0 := by
      rw [picDegreeMod_toPic_boundaryDivisor, ← ha]
      simp [c, ξ]
    have : Nonempty C := ⟨j (Classical.arbitrary U)⟩
    have hE' : Divisor.toPic k C E ∈ (picDegreeMod (k := k) (X := C) N).ker := hE
    rw [ker_picDegreeMod N (Nat.pos_of_ne_zero (NeZero.ne N))] at hE'
    obtain ⟨L, hL⟩ := hE'
    -- so `E = N E' + div f`
    obtain ⟨e, he⟩ := exists_divisorClassGroup_addEquiv_pic (k := k) (C := C)
    obtain ⟨q, hq⟩ := e.surjective L
    obtain ⟨E', rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [he] at hq
    have hprin : E - (N : ℤ) • E' ∈ C.principalDivisors := by
      rw [← QuotientAddGroup.eq_zero_iff, ← e.map_eq_zero_iff, he, map_sub, map_zsmul, hq]
      exact sub_eq_zero.2 hL.symm
    obtain ⟨F, hF⟩ := hprin
    set f : C.functionField := ((Additive.toMul F : C.functionFieldˣ) : C.functionField)
    have hf0 : f ≠ 0 := F.toMul.ne_zero
    have hord (P : closedPoints C) : C.ord f P = E P - N * E' P := by
      have := congrArg (fun D : C.Divisor ↦ D P) hF
      simpa using this
    -- `f` is a unit on a nonempty open `W`
    obtain ⟨W, hWne, s, hs, hsf⟩ := exists_isUnit_germToFunctionField_eq hf0
    have hgW : genericPoint C ∈ W := by
      obtain ⟨⟨w, hw⟩⟩ := hWne
      exact ((genericPoint_spec C).specializes (Set.mem_univ w)).mem_open W.isOpen hw
    have hgU : genericPoint C ∈ Set.range j.base := by
      obtain ⟨u⟩ := (inferInstance : Nonempty U)
      exact ((genericPoint_spec C).specializes (Set.mem_univ (j u))).mem_open
        j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩
    obtain ⟨u₁, hu₁⟩ := hgU
    -- the Kummer torsor of `f` on `U' = U ∩ W`
    let U' : U.Opens := j ⁻¹ᵁ W
    have : Nonempty U' := ⟨⟨u₁, show j u₁ ∈ W by rw [hu₁]; exact hgW⟩⟩
    have : ConnectedSpace U' := FiniteEtale.connectedSpace_of_isOpenImmersion (U'.ι ≫ j)
    let m : U'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (U'.ι ≫ j) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      exact w.2)
    set g : Γ(U', ⊤) := m.appTop (W.topIso.inv s)
    have hg : IsUnit g := (hs.map W.topIso.inv.hom).map m.appTop.hom
    have hgf : toFunctionField (U'.ι ≫ j) g = f :=
      (toFunctionField_appTop_topIso_inv (U'.ι ≫ j) W m (IsOpenImmersion.lift_fac _ _ _) s
        hgW).trans hsf
    obtain ⟨T', hT'⟩ := exists_residue_eq_ord_of_isUnit (U'.ι ≫ j) p hζ hg
    rw [hgf] at hT'
    -- it extends to `U`
    have hext : ∀ y ∈ Set.range j.base, y ∉ Set.range (U'.ι ≫ j).base →
        T'.residue (U'.ι ≫ j) p y = 0 := fun y hy hy' ↦ by
      refine addMonoidHom_ext_rootsOfUnity hζ ?_
      have hyc := isClosed_singleton_of_notMem_range k (U'.ι ≫ j) hy'
      rw [hT', AddMonoidHom.zero_apply, show y = (⟨y, hyc⟩ : closedPoints C).1 from rfl, hord,
        boundaryDivisor_apply_of_mem_range j _ _ hy]
      simp
    obtain ⟨T, hT⟩ := exists_isIsomorphic_pullback_of_residue_eq_zero (p := p) U'.ι T' hext
    refine ⟨classH1 _ U ⟦T⟧, funext fun z ↦ ?_⟩
    rw [residueH1_classH1, ← residue_pullback j U'.ι p T,
      congrFun (residue_eq_of_isIsomorphic (U'.ι ≫ j) p hT) z.1]
    refine addMonoidHom_ext_rootsOfUnity hζ ?_
    rw [hT', show z.1 = (boundaryClosedPoint k j z).1 from rfl, hord,
      boundaryDivisor_apply_boundaryClosedPoint]
    simp [c, ξ]

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the **residue sequence** (5.1)

`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → H⁰(D, ℤ / N (-1)) → H²(C, ℤ / N)`

is exact, for `C` a smooth proper connected curve over an algebraically closed field `k`,
`U ⊆ C` a nonempty open with boundary `D` and `N` invertible in `k`. The maps are the
restriction (`AlgebraicGeometry.Scheme.EtaleTorsor.restrictH1`), the residue
(`AlgebraicGeometry.Scheme.EtaleTorsor.residueH1`) and the Gysin map
(`AlgebraicGeometry.Scheme.gysinH2`). -/
theorem residueSequence_exact (N : ℕ) [NeZero N] [NeZero (N : k)] :
    Function.Injective (restrictH1 (ULift.{u + 1} (ZMod N)) j) ∧
      Function.Exact (restrictH1 (ULift.{u + 1} (ZMod N)) j)
        (residueH1 j (C ↘ Spec (.of k)) N) ∧
      Function.Exact (residueH1 j (C ↘ Spec (.of k)) N) (gysinH2 k j N) := by
  have : IsCurve (C ↘ Spec (.of k)) := inferInstance
  have : Smooth (C ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular C := IsRegular.of_smooth (C ↘ Spec (.of k))
  refine ⟨injective_restrictH1 (j := j), fun y ↦ ?_, fun y ↦ ?_⟩
  · rw [← AddMonoidHom.mem_ker, ← range_restrictH1_eq_ker_residueH1 (p := C ↘ Spec (.of k)) N,
      AddMonoidHom.mem_range]
    exact Iff.rfl
  · rw [← AddMonoidHom.mem_ker, ← range_residueH1_eq_ker_gysinH2, AddMonoidHom.mem_range]
    exact Iff.rfl

end Gysin

end AlgebraicGeometry.Scheme
