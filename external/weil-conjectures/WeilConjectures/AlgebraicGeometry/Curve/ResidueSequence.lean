/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# The residue sequence of a module on an integral scheme

Let `X` be an integral scheme over a field `k` with function field `K` and generic point `η`.
Let `V` be a `K`-vector space and `φ : M ⟶ V_η` a morphism from an `𝒪_X`-module `M` to the
skyscraper module at `η` with value `V` (the "constant sheaf" `U ↦ V`, `U ≠ ∅`), injective on
sections; for instance `M = 𝒪_X` and `V = K`, or `M = Ω¹_{X/k}` and `V = Ω[K⁄k]`.
For a point `x` write `V_x ⊆ V` (`AlgebraicGeometry.Scheme.Modules.stalkLattice`) for the
`k`-subspace of values `φ(s)` of the sections `s` of `M` over open neighbourhoods of `x`.

The *sheaf of principal parts* `𝒫 = AlgebraicGeometry.Scheme.Modules.principalParts φ` has as
sections over `U` the families `(s_x)_{x ∈ U}`, `s_x ∈ V ⧸ V_x`, which are locally of the form
`(v mod V_x)_x` for a single `v ∈ V`. We show that
```
  0 ⟶ M ⟶ V_η ⟶ 𝒫 ⟶ 0
```
is a short exact sequence of `𝒪_X`-modules (`AlgebraicGeometry.Scheme.Modules.shortExact_residue`)
whose middle term is flasque, so that the connecting map identifies
`H¹(X, M) ≅ Γ(X, 𝒫) ⧸ V` (`AlgebraicGeometry.Scheme.Modules.residueH1Equiv`), canonically and
`Γ(X, 𝒪_X)`-linearly.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- On an irreducible scheme every nonempty open contains the generic point. -/
lemma genericPoint_mem_of_mem [IrreducibleSpace X] {U : X.Opens} {x : X} (hx : x ∈ U) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

/-- A `k`-algebra structure on the function field of a `k`-scheme is *compatible* if it is the
composite `k → Γ(X, 𝒪_X) → K` of the structure map and the germ at the generic point. -/
class IsFunctionFieldAlgebra (k : Type u) [Field k] (X : Scheme.{u}) [IrreducibleSpace X]
    [X.Over (Spec (.of k))] [Algebra k X.functionField] : Prop where
  algebraMap_eq (c : k) : algebraMap k X.functionField c =
    X.presheaf.germ ⊤ (genericPoint X) trivial (globalSectionsRingHom k (X := X) c)

namespace Modules

variable [IsIntegral X] (k : Type u) [Field k] [Algebra k X.functionField]
  {V : Type u} [AddCommGroup V] [Module X.functionField V] [Module k V]
  [IsScalarTower k X.functionField V] {M : X.Modules}

section GenericValue

variable {k} (φ : M ⟶ skyscraper (genericPoint X) V)

/-- The value in `V` of a section of `M` under `φ : M ⟶ V_η`. -/
noncomputable def genericValue {U : X.Opens} (h : genericPoint X ∈ U) (s : Γ(M, U)) : V :=
  (show SkyscraperSections (genericPoint X) V U from φ.app U s) ⟨h⟩

@[simp]
lemma genericValue_add {U : X.Opens} (h : genericPoint X ∈ U) (s t : Γ(M, U)) :
    genericValue φ h (s + t) = genericValue φ h s + genericValue φ h t := by
  simp [genericValue, map_add]
  rfl

@[simp]
lemma genericValue_zero {U : X.Opens} (h : genericPoint X ∈ U) :
    genericValue φ h (0 : Γ(M, U)) = 0 := by
  simp [genericValue, map_zero]
  rfl

@[simp]
lemma genericValue_neg {U : X.Opens} (h : genericPoint X ∈ U) (s : Γ(M, U)) :
    genericValue φ h (-s) = -genericValue φ h s := by
  simp [genericValue, map_neg]
  rfl

lemma genericValue_smul {U : X.Opens} (h : genericPoint X ∈ U) (a : Γ(X, U)) (s : Γ(M, U)) :
    genericValue φ h (a • s) = X.presheaf.germ U _ h a • genericValue φ h s := by
  simp only [genericValue, Hom.app_smul]
  rfl

lemma genericValue_res {U U' : X.Opens} (i : U' ≤ U) (h : genericPoint X ∈ U')
    (s : Γ(M, U)) :
    genericValue φ h (M.presheaf.map (homOfLE i).op s) = genericValue φ (i h) s := by
  simp only [genericValue, Hom.app_presheaf_map]
  rfl

variable (k) in
/-- Multiplication by the germ at the generic point of a section `a` of `𝒪_X`, as a
`k`-linear endomorphism of `V`. -/
noncomputable def germSMulLinear {U : X.Opens} (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    V →ₗ[k] V :=
  ((X.presheaf.germ U _ h a) • LinearMap.id : V →ₗ[X.functionField] V).restrictScalars k

@[simp]
lemma germSMulLinear_apply {U : X.Opens} (h : genericPoint X ∈ U) (a : Γ(X, U)) (v : V) :
    germSMulLinear k h a v = X.presheaf.germ U _ h a • v :=
  rfl

variable [X.Over (Spec (.of k))] [IsFunctionFieldAlgebra k X]

variable (k) in
/-- The `k`-subspace `V_x ⊆ V` of values `φ(s)` of the sections `s` of `M` over open
neighbourhoods of `x`; for `φ` the inclusion of `𝒪_X` into the constant sheaf `K` this is the
local ring `𝒪_{X,x} ⊆ K`. -/
noncomputable def stalkLattice (x : X) : Submodule k V where
  carrier := {v | ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)),
    genericValue φ (genericPoint_mem_of_mem hx) s = v}
  zero_mem' := ⟨⊤, trivial, 0, genericValue_zero _ _⟩
  add_mem' := by
    rintro _ _ ⟨U, hU, s, rfl⟩ ⟨U', hU', s', rfl⟩
    refine ⟨U ⊓ U', ⟨hU, hU'⟩, M.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s +
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op s', ?_⟩
    rw [genericValue_add, genericValue_res, genericValue_res]
  smul_mem' c := by
    rintro _ ⟨U, hU, s, rfl⟩
    refine ⟨U, hU, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (globalSectionsRingHom k (X := X) c) • s, ?_⟩
    rw [genericValue_smul, X.presheaf.germ_res_apply, ← IsFunctionFieldAlgebra.algebraMap_eq,
      algebraMap_smul]

lemma mem_stalkLattice {x : X} {v : V} :
    v ∈ stalkLattice k φ x ↔ ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)),
      genericValue φ (genericPoint_mem_of_mem hx) s = v :=
  Iff.rfl

lemma genericValue_mem_stalkLattice {U : X.Opens} {x : X} (hx : x ∈ U) (s : Γ(M, U)) :
    genericValue φ (genericPoint_mem_of_mem hx) s ∈ stalkLattice k φ x :=
  ⟨U, hx, s, rfl⟩

lemma germ_smul_mem_stalkLattice {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)) {v : V}
    (hv : v ∈ stalkLattice k φ x) :
    X.presheaf.germ U _ (genericPoint_mem_of_mem hx) a • v ∈ stalkLattice k φ x := by
  obtain ⟨U', hU', s, rfl⟩ := hv
  refine ⟨U ⊓ U', ⟨hx, hU'⟩, X.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op a •
    M.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op s, ?_⟩
  rw [genericValue_smul, genericValue_res, X.presheaf.germ_res_apply]

end GenericValue

/-! ### The sheaf of principal parts -/

section PrincipalParts

variable [X.Over (Spec (.of k))] [IsFunctionFieldAlgebra k X] {k}
  (φ : M ⟶ skyscraper (genericPoint X) V)

/-- Multiplication by a section `a` of `𝒪_X` over `U ∋ x` on `V ⧸ V_x`. -/
noncomputable def quotSMul {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)) :
    V ⧸ stalkLattice k φ x →ₗ[k] V ⧸ stalkLattice k φ x :=
  (stalkLattice k φ x).mapQ (stalkLattice k φ x) (germSMulLinear k (genericPoint_mem_of_mem hx) a)
    fun _ hv ↦ germ_smul_mem_stalkLattice φ hx a hv

@[simp]
lemma quotSMul_mk {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)) (v : V) :
    quotSMul φ hx a (Submodule.Quotient.mk v : V ⧸ stalkLattice k φ x) =
      Submodule.Quotient.mk (X.presheaf.germ U _ (genericPoint_mem_of_mem hx) a • v) :=
  rfl

lemma quotSMul_one {U : X.Opens} {x : X} (hx : x ∈ U) (q : V ⧸ stalkLattice k φ x) :
    quotSMul φ hx 1 q = q := by
  induction q using Submodule.Quotient.induction_on with
  | _ v => rw [quotSMul_mk, map_one, one_smul]

lemma quotSMul_zero {U : X.Opens} {x : X} (hx : x ∈ U) (q : V ⧸ stalkLattice k φ x) :
    quotSMul φ hx 0 q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | _ v => rw [quotSMul_mk, map_zero, zero_smul, Submodule.Quotient.mk_zero]

lemma quotSMul_mul {U : X.Opens} {x : X} (hx : x ∈ U) (a b : Γ(X, U))
    (q : V ⧸ stalkLattice k φ x) :
    quotSMul φ hx (a * b) q = quotSMul φ hx a (quotSMul φ hx b q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ v => rw [quotSMul_mk, quotSMul_mk, quotSMul_mk, map_mul, mul_smul]

lemma quotSMul_add {U : X.Opens} {x : X} (hx : x ∈ U) (a b : Γ(X, U))
    (q : V ⧸ stalkLattice k φ x) :
    quotSMul φ hx (a + b) q = quotSMul φ hx a q + quotSMul φ hx b q := by
  induction q using Submodule.Quotient.induction_on with
  | _ v => rw [quotSMul_mk, quotSMul_mk, quotSMul_mk, map_add, add_smul,
      Submodule.Quotient.mk_add]

variable (k) in
/-- The sections over `U` of the sheaf of principal parts: families `(s_x)_{x ∈ U}` with
`s_x ∈ V ⧸ V_x` which are, locally on `U`, the classes of a single element of `V`. -/
noncomputable def principalPartsSections (U : X.Opens) :
    AddSubgroup ((x : U) → V ⧸ stalkLattice k φ x.1) where
  carrier := {s | ∀ x : U, ∃ W : X.Opens, W ≤ U ∧ x.1 ∈ W ∧ ∃ v : V,
    ∀ y : U, y.1 ∈ W → s y = Submodule.Quotient.mk v}
  zero_mem' x := ⟨U, le_rfl, x.2, 0, fun _ _ ↦ (Submodule.Quotient.mk_zero _).symm⟩
  add_mem' {s t} hs ht x := by
    obtain ⟨W, hW, hxW, v, hv⟩ := hs x
    obtain ⟨W', -, hxW', v', hv'⟩ := ht x
    refine ⟨W ⊓ W', inf_le_left.trans hW, ⟨hxW, hxW'⟩, v + v', fun y hy ↦ ?_⟩
    rw [Pi.add_apply, hv y hy.1, hv' y hy.2, Submodule.Quotient.mk_add]
  neg_mem' {s} hs x := by
    obtain ⟨W, hW, hxW, v, hv⟩ := hs x
    refine ⟨W, hW, hxW, -v, fun y hy ↦ ?_⟩
    rw [Pi.neg_apply, hv y hy, Submodule.Quotient.mk_neg]

variable (k) in
/-- The sections over `U` of the sheaf of principal parts, as a type. -/
def PrincipalParts (U : X.Opens) : Type u := principalPartsSections k φ U

namespace PrincipalParts

variable {U : X.Opens}

noncomputable instance : AddCommGroup (PrincipalParts k φ U) :=
  inferInstanceAs (AddCommGroup (principalPartsSections k φ U))

/-- The component at `x` of a principal part. -/
def val (s : PrincipalParts k φ U) (x : U) : V ⧸ stalkLattice k φ x.1 :=
  (show principalPartsSections k φ U from s).1 x

lemma property (s : PrincipalParts k φ U) (x : U) : ∃ W : X.Opens, W ≤ U ∧ x.1 ∈ W ∧ ∃ v : V,
    ∀ y : U, y.1 ∈ W → s.val φ y = Submodule.Quotient.mk v :=
  (show principalPartsSections k φ U from s).2 x

/-- Constructor for principal parts. -/
def mk (s : (x : U) → V ⧸ stalkLattice k φ x.1)
    (hs : ∀ x : U, ∃ W : X.Opens, W ≤ U ∧ x.1 ∈ W ∧ ∃ v : V,
      ∀ y : U, y.1 ∈ W → s y = Submodule.Quotient.mk v) : PrincipalParts k φ U :=
  (⟨s, hs⟩ : principalPartsSections k φ U)

@[simp]
lemma val_mk (s : (x : U) → V ⧸ stalkLattice k φ x.1) (hs) (x : U) :
    (mk φ s hs).val φ x = s x :=
  rfl

@[ext]
lemma ext {s t : PrincipalParts k φ U} (h : ∀ x, s.val φ x = t.val φ x) : s = t :=
  Subtype.ext (funext h)

@[simp]
lemma add_val (s t : PrincipalParts k φ U) (x : U) :
    (s + t).val φ x = s.val φ x + t.val φ x :=
  rfl

@[simp]
lemma zero_val (x : U) : (0 : PrincipalParts k φ U).val φ x = 0 :=
  rfl

@[simp]
lemma neg_val (s : PrincipalParts k φ U) (x : U) : (-s).val φ x = -s.val φ x :=
  rfl

@[simp]
lemma sub_val (s t : PrincipalParts k φ U) (x : U) :
    (s - t).val φ x = s.val φ x - t.val φ x :=
  rfl

noncomputable instance : SMul Γ(X, U) (PrincipalParts k φ U) where
  smul a s := mk φ (fun x ↦ quotSMul φ x.2 a (s.val φ x)) fun x ↦ by
    obtain ⟨W, hW, hxW, v, hv⟩ := s.property φ x
    exact ⟨W, hW, hxW, X.presheaf.germ U _ (genericPoint_mem_of_mem x.2) a • v,
      fun y hy ↦ by rw [hv y hy, quotSMul_mk]⟩

@[simp]
lemma smul_val (a : Γ(X, U)) (s : PrincipalParts k φ U) (x : U) :
    (a • s).val φ x = quotSMul φ x.2 a (s.val φ x) :=
  rfl

noncomputable instance : Module Γ(X, U) (PrincipalParts k φ U) where
  one_smul _ := ext φ fun x ↦ quotSMul_one φ x.2 _
  mul_smul a b _ := ext φ fun x ↦ quotSMul_mul φ x.2 a b _
  smul_zero _ := ext φ fun _ ↦ map_zero _
  smul_add _ _ _ := ext φ fun _ ↦ map_add _ _ _
  add_smul a b _ := ext φ fun x ↦ quotSMul_add φ x.2 a b _
  zero_smul _ := ext φ fun x ↦ quotSMul_zero φ x.2 _

/-- Restriction of principal parts. -/
noncomputable def res {U U' : X.Opens} (i : U' ≤ U) :
    PrincipalParts k φ U →+ PrincipalParts k φ U' where
  toFun s := mk φ (fun y ↦ s.val φ ⟨y.1, i y.2⟩) fun x ↦ by
    obtain ⟨W, -, hxW, v, hv⟩ := s.property φ ⟨x.1, i x.2⟩
    exact ⟨W ⊓ U', inf_le_right, ⟨hxW, x.2⟩, v, fun y hy ↦ hv _ hy.1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma res_val {U U' : X.Opens} (i : U' ≤ U) (s : PrincipalParts k φ U) (y : U') :
    (res φ i s).val φ y = s.val φ ⟨y.1, i y.2⟩ :=
  rfl

end PrincipalParts

variable (k) in
/-- The presheaf of abelian groups underlying the sheaf of principal parts. -/
noncomputable def principalPartsPresheafAb : X.Opensᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (PrincipalParts k φ U.unop)
  map i := AddCommGrpCat.ofHom (PrincipalParts.res φ i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable instance (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((principalPartsPresheafAb k φ).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (PrincipalParts k φ U.unop))

lemma principalPartsPresheafAb_map_smul {U U' : X.Opensᵒᵖ} (i : U ⟶ U')
    (a : X.ringCatSheaf.obj.obj U) (s : (principalPartsPresheafAb k φ).obj U) :
    (principalPartsPresheafAb k φ).map i (a • s) =
      X.ringCatSheaf.obj.map i a • (principalPartsPresheafAb k φ).map i s := by
  refine PrincipalParts.ext φ fun y ↦ ?_
  let s' : PrincipalParts k φ U.unop := s
  let a' : Γ(X, U.unop) := a
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (s'.val φ ⟨y.1, i.unop.le y.2⟩)
  change quotSMul φ (i.unop.le y.2) a' (s'.val φ ⟨y.1, i.unop.le y.2⟩) =
    quotSMul φ y.2 (X.presheaf.map i.unop.op a') (s'.val φ ⟨y.1, i.unop.le y.2⟩)
  rw [← hv, quotSMul_mk, quotSMul_mk, X.presheaf.germ_res_apply]

lemma isSheaf_principalPartsPresheafAb :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (principalPartsPresheafAb k φ) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget Ab.{u}),
    isSheaf_iff_isSheaf_of_type]
  intro U S hS s hs
  let s' : ∀ ⦃W : X.Opens⦄ (f : W ⟶ U), S f → PrincipalParts k φ W := fun W f hf ↦ s f hf
  have hs' {W W' : X.Opens} (f : W ⟶ U) (g : W' ⟶ U) (hf : S f) (hg : S g) (x : X)
      (hxW : x ∈ W) (hxW' : x ∈ W') :
      (s' f hf).val φ ⟨x, hxW⟩ = (s' g hg).val φ ⟨x, hxW'⟩ := by
    have := hs (homOfLE (inf_le_left : W ⊓ W' ≤ W)) (homOfLE inf_le_right) hf hg
      (Subsingleton.elim _ _)
    exact congr_arg (fun t : PrincipalParts k φ (W ⊓ W') ↦ t.val φ ⟨x, hxW, hxW'⟩) this
  choose W f hf hW using hS
  let g : PrincipalParts k φ U := PrincipalParts.mk φ
    (fun x ↦ (s' (f x.1 x.2) (hf x.1 x.2)).val φ ⟨x.1, hW x.1 x.2⟩) fun x ↦ by
      obtain ⟨W', hW', hxW', v, hv⟩ :=
        (s' (f x.1 x.2) (hf x.1 x.2)).property φ ⟨x.1, hW x.1 x.2⟩
      refine ⟨W', hW'.trans (f x.1 x.2).le, hxW', v, fun y hy ↦ ?_⟩
      rw [hs' _ (f x.1 x.2) _ (hf x.1 x.2) y.1 _ (hW' hy)]
      exact hv ⟨y.1, hW' hy⟩ hy
  refine ⟨g, fun W' f' hf' ↦ ?_, fun t ht ↦ ?_⟩
  · refine PrincipalParts.ext φ fun y ↦ ?_
    exact hs' _ _ _ _ _ _ _
  · refine PrincipalParts.ext φ fun y ↦ ?_
    have := congr_arg (fun t : PrincipalParts k φ (W y.1 y.2) ↦ t.val φ ⟨y.1, hW y.1 y.2⟩)
      (ht (f y.1 y.2) (hf y.1 y.2))
    exact this

variable (k) in
/-- The **sheaf of principal parts** of `φ : M ⟶ V_η`: its sections over `U` are the families
`(s_x)_{x ∈ U}`, `s_x ∈ V ⧸ V_x`, which are locally the classes of a single element of `V`. -/
noncomputable def principalParts : X.Modules where
  val := PresheafOfModules.ofPresheaf (principalPartsPresheafAb k φ)
    fun _ _ i a s ↦ principalPartsPresheafAb_map_smul φ i a s
  isSheaf := isSheaf_principalPartsPresheafAb φ

end PrincipalParts

/-! ### The residue sequence -/

omit [IsIntegral X] in
/-- Every skyscraper module is flasque. -/
lemma isFlasque_skyscraper (x : X) (I : Type u) [AddCommGroup I] [Module (X.presheaf.stalk x) I] :
    TopCat.Presheaf.IsFlasque (skyscraper x I).presheaf where
  epi {U U'} i := by
    classical
    refine (AddCommGrpCat.epi_iff_surjective _).mpr fun t ↦ ?_
    refine ⟨show SkyscraperSections x I U.unop from
      fun _ ↦ if h : x ∈ U'.unop then t ⟨h⟩ else 0, ?_⟩
    refine SkyscraperSections.ext fun h ↦ ?_
    change (if h' : x ∈ U'.unop then t ⟨h'⟩ else 0) = _
    rw [dite_eq_left h]

section ResidueSequence

variable [X.Over (Spec (.of k))] [IsFunctionFieldAlgebra k X] {k}
  (φ : M ⟶ skyscraper (genericPoint X) V)

/-- The principal parts of a section of the constant sheaf `V_η`. -/
noncomputable def toPrincipalPartsApp (U : X.Opens) :
    SkyscraperSections (genericPoint X) V U →+ PrincipalParts k φ U where
  toFun t := PrincipalParts.mk φ
    (fun y ↦ Submodule.Quotient.mk (t ⟨genericPoint_mem_of_mem y.2⟩))
    fun x ↦ ⟨U, le_rfl, x.2, t ⟨genericPoint_mem_of_mem x.2⟩, fun _ _ ↦ rfl⟩
  map_zero' := PrincipalParts.ext φ fun _ ↦ Submodule.Quotient.mk_zero _
  map_add' _ _ := PrincipalParts.ext φ fun _ ↦ Submodule.Quotient.mk_add _

/-- The morphism of presheaves underlying `V_η ⟶ 𝒫`. -/
noncomputable def toPrincipalPartsPresheafHom :
    (skyscraper (genericPoint X) V).presheaf ⟶ (principalParts k φ).presheaf where
  app U := AddCommGrpCat.ofHom (toPrincipalPartsApp φ U.unop)
  naturality _ _ _ := rfl

variable (k) in
/-- The morphism `V_η ⟶ 𝒫` from the constant sheaf to the sheaf of principal parts, sending a
section `v` over `U` to the family of its classes `(v mod V_x)_{x ∈ U}`. -/
noncomputable def toPrincipalParts : skyscraper (genericPoint X) V ⟶ principalParts k φ :=
  ⟨PresheafOfModules.homMk (toPrincipalPartsPresheafHom φ) fun _ _ _ ↦ rfl⟩

lemma toPrincipalParts_app_val {U : X.Opens} (t : Γ(skyscraper (genericPoint X) V, U)) (y : U) :
    PrincipalParts.val φ (show PrincipalParts k φ U from (toPrincipalParts k φ).app U t) y =
      Submodule.Quotient.mk
        ((show SkyscraperSections (genericPoint X) V U from t) ⟨genericPoint_mem_of_mem y.2⟩) :=
  rfl

variable (k) in
/-- The **residue sequence** `0 ⟶ M ⟶ V_η ⟶ 𝒫 ⟶ 0` as a short complex. -/
noncomputable def residueShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk φ (toPrincipalParts k φ) (by
    ext U s
    refine PrincipalParts.ext φ fun y ↦ ?_
    exact (Submodule.Quotient.mk_eq_zero _).2 (genericValue_mem_stalkLattice φ y.2 s))

variable {φ} (hφ : ∀ U, Function.Injective (φ.app U))
include hφ

/-- A section of the constant sheaf `V_η` over `U` whose value lies in `V_x` for every `x ∈ U`
comes from a section of `M`: glue the local sections witnessing `v ∈ V_x`. -/
theorem exists_app_eq_of_forall_mem {U : X.Opens} (t : SkyscraperSections (genericPoint X) V U)
    (ht : ∀ (y : X) (hy : y ∈ U), t ⟨genericPoint_mem_of_mem hy⟩ ∈ stalkLattice k φ y) :
    ∃ s : Γ(M, U), φ.app U s = t := by
  by_cases hη : genericPoint X ∈ U
  swap
  · exact ⟨0, SkyscraperSections.ext fun h ↦ (hη h).elim⟩
  have ht' (y : U) : ∃ (W : X.Opens) (hyW : y.1 ∈ W) (s : Γ(M, W)),
      genericValue φ (genericPoint_mem_of_mem hyW) s = t ⟨hη⟩ := ht y.1 y.2
  choose W hyW s hs using ht'
  let F : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩
  let W' : U → X.Opens := fun y ↦ W y ⊓ U
  let s' : ∀ y, Γ(M, W' y) := fun y ↦ M.presheaf.map (homOfLE inf_le_left).op (s y)
  have hs' (y : U) (h : genericPoint X ∈ W' y) : genericValue φ h (s' y) = t ⟨hη⟩ := by
    rw [genericValue_res]
    exact hs y
  obtain ⟨g, hg, -⟩ := F.existsUnique_gluing' (U := W') U (fun y ↦ homOfLE inf_le_right)
    (fun y hy ↦ Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyW ⟨y, hy⟩, hy⟩) s' (by
      intro y z
      apply hφ
      refine SkyscraperSections.ext fun h ↦ ?_
      change genericValue φ h (M.presheaf.map (homOfLE inf_le_left).op (s' y)) =
        genericValue φ h (M.presheaf.map (homOfLE inf_le_right).op (s' z))
      rw [genericValue_res, genericValue_res, genericValue_res, genericValue_res, hs, hs])
  refine ⟨g, SkyscraperSections.ext fun h ↦ ?_⟩
  have := hg ⟨genericPoint X, hη⟩
  change genericValue φ h g = _
  have h' : genericPoint X ∈ W' ⟨genericPoint X, hη⟩ := ⟨hyW _, hη⟩
  rw [← genericValue_res φ inf_le_right h', ← hs' _ h']
  exact congr_arg (genericValue φ h') this

lemma mono_of_injective_app : Mono φ :=
  ⟨fun g h e ↦ by
    ext U a
    have h1 : (g ≫ φ).app U a = (h ≫ φ).app U a := by rw [e]
    exact hφ U h1⟩

/-- **The residue sequence is exact**: for `φ : M ⟶ V_η` injective on sections,
`0 ⟶ M ⟶ V_η ⟶ 𝒫 ⟶ 0` is a short exact sequence of `𝒪_X`-modules. -/
theorem shortExact_residue : (residueShortComplex k φ).ShortExact := by
  have : Mono (residueShortComplex k φ).f := mono_of_injective_app hφ
  refine ShortComplex.ShortExact.mk' ?_ this ?_
  · refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {A} g hg ↦ ?_)
    have key (U : X.Opens) (a : Γ(A, U)) : ∃ s : Γ(M, U), φ.app U s = g.app U a := by
      refine exists_app_eq_of_forall_mem (k := k) hφ _ fun y hy ↦ ?_
      have h0 : (g ≫ toPrincipalParts k φ).app U a = 0 := by
        rw [show g ≫ toPrincipalParts k φ = 0 from hg]
        rfl
      have := congr_arg (fun t : PrincipalParts k φ U ↦ t.val φ ⟨y, hy⟩) h0
      exact (Submodule.Quotient.mk_eq_zero _).1 this
    choose l hl using key
    let l' : A.presheaf ⟶ M.presheaf :=
      { app U := AddCommGrpCat.ofHom
          { toFun := l U.unop
            map_zero' := hφ _ (by rw [hl, map_zero, map_zero])
            map_add' a b := hφ _ (by rw [hl, map_add, map_add, hl, hl]) }
        naturality U U' i := by
          ext a
          apply hφ
          change φ.app _ (l _ _) = φ.app _ (M.presheaf.map (homOfLE i.unop.le).op (l _ _))
          rw [Hom.app_presheaf_map, hl, hl]
          exact Hom.app_presheaf_map g (homOfLE i.unop.le) a }
    refine ⟨⟨PresheafOfModules.homMk l' fun U r a ↦ hφ _ ?_⟩, ?_⟩
    · erw [Hom.app_smul, hl, hl]
      exact Hom.app_smul g r a
    · ext U a
      exact hl U a
  · refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
    obtain ⟨W', hW', hxW', v, hv⟩ := PrincipalParts.property φ (show PrincipalParts k φ W from y)
      ⟨x, hx⟩
    refine ⟨W', hW', hxW', show SkyscraperSections (genericPoint X) V W' from fun _ ↦ v, ?_⟩
    refine PrincipalParts.ext φ fun z ↦ ?_
    exact (hv ⟨z.1, hW' z.2⟩ z.2).symm

omit [IsIntegral X] hφ in
lemma subsingleton_H_one_skyscraper (x : X) (I : Type u) [AddCommGroup I]
    [Module (X.presheaf.stalk x) I] : Subsingleton ((skyscraper x I).H 1) :=
  have : TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (skyscraper x I)).obj :=
    isFlasque_skyscraper x I
  TopCat.Sheaf.IsFlasque.subsingleton_H 0 ((SheafOfModules.toSheaf X.ringCatSheaf).obj _)

variable (k) (φ) in
omit hφ in
/-- `V_η ⟶ 𝒫` on global sections, as a `Γ(X, 𝒪_X)`-linear map. -/
noncomputable def toPrincipalPartsTop :
    Γ(skyscraper (genericPoint X) V, ⊤) →ₗ[Γ(X, ⊤)] Γ(principalParts k φ, ⊤) where
  toFun := (toPrincipalParts k φ).app ⊤
  map_add' := map_add _
  map_smul' := Hom.app_smul _

variable (k) in
/-- The connecting map `Γ(X, 𝒫) ⟶ H¹(X, M)` of the residue sequence. -/
noncomputable def residueδ : Γ(principalParts k φ, ⊤) →ₗ[Γ(X, ⊤)] M.H 1 where
  toFun s :=
    H.δ (shortExact_residue (k := k) hφ) 0 ((H.zeroLinearEquiv (principalParts k φ)).symm s)
  map_add' _ _ := by rw [map_add, map_add]
  map_smul' a s := by
    rw [LinearEquiv.map_smul, H.δ_smul]
    rfl

variable (k) in
lemma surjective_residueδ : Function.Surjective (residueδ k hφ) := by
  have : Subsingleton ((residueShortComplex k φ).X₂.H 1) :=
    subsingleton_H_one_skyscraper (genericPoint X) V
  intro z
  obtain ⟨y, hy⟩ := H.surjective_δ_zero (shortExact_residue (k := k) hφ) z
  exact ⟨H.zeroLinearEquiv _ y, by simp [residueδ, hy]⟩

variable (k) in
lemma ker_residueδ :
    LinearMap.ker (residueδ k hφ) = LinearMap.range (toPrincipalPartsTop k φ) := by
  ext s
  have h := SetLike.ext_iff.mp (H.ker_δ_eq_range_map_g (shortExact_residue (k := k) hφ) 0)
    ((H.zeroLinearEquiv (principalParts k φ)).symm s)
  rw [LinearMap.mem_ker]
  refine (h.trans ?_)
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨H.zeroLinearEquiv _ t, ?_⟩
    have := H.zeroLinearEquiv_map (toPrincipalParts k φ) t
    change H.zeroLinearEquiv _ (H.map (toPrincipalParts k φ) 0 t) = _ at this
    rw [show H.map (toPrincipalParts k φ) 0 t = _ from ht, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨t, rfl⟩
    refine ⟨(H.zeroLinearEquiv (skyscraper (genericPoint X) V)).symm t,
      (H.zeroLinearEquiv (principalParts k φ)).injective ?_⟩
    rw [LinearEquiv.apply_symm_apply]
    have := H.zeroLinearEquiv_map (toPrincipalParts k φ)
      ((H.zeroLinearEquiv (skyscraper (genericPoint X) V)).symm t)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this

variable (k) in
/-- **`H¹` via principal parts.** For `φ : M ⟶ V_η` injective on sections, the connecting map
of the residue sequence identifies `H¹(X, M)` with the global principal parts modulo the
principal parts of elements of `V`:
`H¹(X, M) ≅ Γ(X, 𝒫) ⧸ V`, `Γ(X, 𝒪_X)`-linearly. -/
noncomputable def residueH1Equiv :
    M.H 1 ≃ₗ[Γ(X, ⊤)] Γ(principalParts k φ, ⊤) ⧸ LinearMap.range (toPrincipalPartsTop k φ) :=
  (((LinearMap.range (toPrincipalPartsTop k φ)).quotEquivOfEq _ (ker_residueδ k hφ).symm).trans
    ((residueδ k hφ).quotKerEquivOfSurjective (surjective_residueδ k hφ))).symm

variable (k) in
lemma residueH1Equiv_symm_mk (s : Γ(principalParts k φ, ⊤)) :
    (residueH1Equiv k hφ).symm (Submodule.Quotient.mk s) = residueδ k hφ s :=
  rfl

end ResidueSequence

end Modules

end AlgebraicGeometry.Scheme
