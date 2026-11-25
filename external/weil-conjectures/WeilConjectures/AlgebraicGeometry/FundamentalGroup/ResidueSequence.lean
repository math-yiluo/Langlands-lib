/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpen
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Inertia
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorCoefficients
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorResidue

/-!
# The residue sequence of an open curve

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k`, with boundary `D = C ∖ U`, and let `N` be invertible in `k`. The residues
`res_z : H¹(U, ℤ / N) → Hom(μ_N(k), ℤ / N) = ℤ / N (-1)` at the boundary points
(`AlgebraicGeometry.Scheme.EtaleTorsor.residue`) fit in the exact sequence (5.1) of blueprint
`proposition-no-fixed-class-degree-one--1`

`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → ⊕_{z ∈ D} ℤ / N (-1)`.

In the torsor model of `H¹`:

* the residue of a torsor at `z` vanishes if and only if its monodromy is trivial on the kernel
  of `π₁(U) → π₁(U ∪ {z})`
  (`AlgebraicGeometry.Scheme.EtaleTorsor.residue_eq_zero_iff_forall_monodromy_eq_one`): by
  Kummer theory at the generic point, the inertia group at `z` fixes a Kummer element `x` of the
  torsor if and only if `N` divides `ord_z (x ^ N)`;
* a torsor on `U` extends to `C` if and only if all its residues vanish
  (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isIsomorphic_pullback_iff_residue_eq_zero`), and
  torsors on `C` with isomorphic restrictions to `U` are isomorphic
  (`AlgebraicGeometry.Scheme.EtaleTorsor.isIsomorphic_of_isIsomorphic_pullback_of_isRegular`).

In `H¹ = Sheaf.H` of the constant sheaves, with the restriction map
`AlgebraicGeometry.Scheme.EtaleTorsor.restrictH1` and the residue map
`AlgebraicGeometry.Scheme.EtaleTorsor.residueH1`, this is the exactness of (5.1)
(`AlgebraicGeometry.Scheme.EtaleTorsor.injective_restrictH1`,
`AlgebraicGeometry.Scheme.EtaleTorsor.range_restrictH1_eq_ker_residueH1`). Both maps are
compatible with the reduction of coefficients
(`AlgebraicGeometry.Scheme.EtaleTorsor.restrictH1_map`,
`AlgebraicGeometry.Scheme.EtaleTorsor.residueH1_map_castHom`). The Frobenius equivariance and
the boundary module are in
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.ResidueSequenceFrobenius`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

section Residue

variable {C U : Scheme.{u}} [IsIntegral C] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  [IsLocallyNoetherian C] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) {N : ℕ} [NeZero N]
  [NeZero (N : k)] [HasEnoughRootsOfUnity k N]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

lemma residue_apply (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (z : C)
    (ξ : Additive (rootsOfUnity N k)) :
    T.residue j p z ξ = kummerResidue C (T.galoisCharacter j) z
      (algebraMap C.functionField Ω (p.functionFieldConstants ((ξ.toMul : kˣ) : k))) :=
  rfl

/-- Isomorphic torsors have the same residues. -/
lemma residue_eq_of_isIsomorphic {T T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) U}
    (h : T.IsIsomorphic T') : T.residue j p = T'.residue j p := by
  funext z
  refine AddMonoidHom.ext fun ξ ↦ ?_
  rw [residue_apply, residue_apply, galoisCharacter_eq_of_isIsomorphic j h]

/-- The residue against `ξ` is the order of vanishing of `x ^ N` for any Kummer element `x` of
the torsor against `ξ`. -/
lemma residue_eq_ord (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (z : C)
    (ξ : Additive (rootsOfUnity N k)) {x : Ω} {f : C.functionField} (hx : x ≠ 0)
    (hf : algebraMap C.functionField Ω f = x ^ N)
    (hχ : ∀ σ : Gal(Ω/C.functionField), σ x =
      algebraMap C.functionField Ω (p.functionFieldConstants ((ξ.toMul : kˣ) : k)) ^
        (T.galoisCharacter j σ).val * x) :
    T.residue j p z ξ = (C.ord f z : ZMod N) :=
  kummerResidue_eq z hx hf hχ

/-- The residue is additive in the torsor: if the Galois character of `T` is the sum of those of
`T₁` and `T₂`, the residues of `T` are the sums of those of `T₁` and `T₂`. -/
lemma residue_eq_add_of_galoisCharacter_eq_add {T T₁ T₂ : EtaleTorsor (ULift.{u + 1} (ZMod N)) U}
    (h : ∀ σ, T.galoisCharacter j σ = T₁.galoisCharacter j σ + T₂.galoisCharacter j σ)
    (z : C) : T.residue j p z = T₁.residue j p z + T₂.residue j p z := by
  refine AddMonoidHom.ext fun ξ ↦ ?_
  have hξ : ((ξ.toMul : kˣ) : k) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N _).1 ξ.toMul.2, Units.val_one]
  have hξΩ : algebraMap C.functionField Ω (p.functionFieldConstants ((ξ.toMul : kˣ) : k)) ^ N =
      1 := by
    rw [← map_pow, ← map_pow, hξ, map_one, map_one]
  obtain ⟨x₁, f₁, hx₁, hf₁, hχ₁⟩ := T₁.exists_kummerElement j p hξ
  obtain ⟨x₂, f₂, hx₂, hf₂, hχ₂⟩ := T₂.exists_kummerElement j p hξ
  rw [AddMonoidHom.add_apply, residue_apply, residue_apply, residue_apply,
    show T.galoisCharacter j = T₁.galoisCharacter j + T₂.galoisCharacter j from funext h]
  exact kummerResidue_add z hξΩ hx₁ hf₁ hχ₁ hx₂ hf₂ hχ₂

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the residues are compatible with the
reduction of coefficients `ℤ / N d → ℤ / N`.

If the Galois character of a `ℤ / N`-torsor `T'` is the reduction of that of a
`ℤ / N d`-torsor `T`, then the residues of `T'` are the reductions of those of `T`, along the
transition map `Hom(μ_{N d}, ℤ / N d) → Hom(μ_N, ℤ / N)` induced by `ξ ↦ ξ ^ d`. -/
theorem residue_eq_castHom_of_galoisCharacter {d : ℕ} [NeZero (N * d)]
    [NeZero ((N * d : ℕ) : k)] [HasEnoughRootsOfUnity k (N * d)]
    {T : EtaleTorsor (ULift.{u + 1} (ZMod (N * d))) U} {T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) U}
    (h : ∀ σ, T'.galoisCharacter j σ =
      ZMod.castHom (dvd_mul_right N d) (ZMod N) (T.galoisCharacter j σ))
    (z : C) (ξ : rootsOfUnity (N * d) k) (ξ' : rootsOfUnity N k)
    (hξ : ((ξ' : kˣ) : k) = ((ξ : kˣ) : k) ^ d) :
    T'.residue j p z (Additive.ofMul ξ') =
      ZMod.castHom (dvd_mul_right N d) (ZMod N) (T.residue j p z (Additive.ofMul ξ)) := by
  have hξN : ((ξ : kˣ) : k) ^ (N * d) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ξ.2, Units.val_one]
  obtain ⟨x, f, hx, hf, hχ⟩ := T.exists_kummerElement j p hξN
  set ξΩ := algebraMap C.functionField Ω (p.functionFieldConstants ((ξ : kˣ) : k)) with hξΩdef
  have hξΩ : ξΩ ^ (N * d) = 1 := by rw [hξΩdef, ← map_pow, ← map_pow, hξN, map_one, map_one]
  rw [T.residue_eq_ord j p z (Additive.ofMul ξ) hx hf hχ]
  rw [T'.residue_eq_ord j p z (Additive.ofMul ξ') (x := x ^ d) (f := f) (pow_ne_zero _ hx)
    (by rw [hf, ← pow_mul, mul_comm]) ?_]
  · rw [map_intCast]
  · intro σ
    have hξ' : algebraMap C.functionField Ω
        (p.functionFieldConstants (((Additive.ofMul ξ').toMul : kˣ) : k)) = ξΩ ^ d := by
      rw [hξΩdef, ← map_pow, ← map_pow, ← hξ]
      rfl
    rw [hξ', map_pow, hχ σ, h σ, mul_pow, ← pow_mul, ← pow_mul, ZMod.castHom_apply,
      ZMod.cast_eq_val, ZMod.val_natCast]
    congr 1
    set a := (T.galoisCharacter j σ).val
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [show (a % N + N * (a / N)) * d = d * (a % N) + N * d * (a / N) by ring, pow_add,
      pow_mul ξΩ (N * d), hξΩ, one_pow, mul_one]

end Residue

section H1

/-! ### The residue sequence in `H¹` -/

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M]

lemma classH1_out {Y : Scheme.{u}}
    (x : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    classH1 M Y ⟦((classH1Equiv M Y).symm x).out⟧ = x := by
  rw [Quotient.out_eq, ← classH1Equiv_apply, Equiv.apply_symm_apply]

lemma classH1_eq_classH1_iff {Y : Scheme.{u}} {t t' : EtaleTorsor M Y} :
    classH1 M Y ⟦t⟧ = classH1 M Y ⟦t'⟧ ↔ t.IsIsomorphic t' :=
  ⟨fun h ↦ Quotient.exact (injective_classH1 h), fun h ↦ congrArg _ (Quotient.sound h)⟩

variable [TopologicalSpace M] [DiscreteTopology M]

lemma monodromy_out {Y : Scheme.{u}} [ConnectedSpace Y] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (s : Spec (.of Ω') ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (x : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    ((classH1Equiv M Y).symm x).out.monodromy s G = sheafHEquivContinuousMonoidHom M s G x := by
  rw [← sheafHEquivContinuousMonoidHom_classH1, classH1_out]

variable {C U : Scheme.{u}} [IsIntegral C] [ConnectedSpace C] [ConnectedSpace U] (j : U ⟶ C)
  [IsOpenImmersion j] [Nonempty U]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

variable (M) in
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the restriction map
`j^* : H¹(C, M) → H¹(U, M)` of the residue sequence, in the torsor model of `H¹`: the class of a
torsor `T` on `C` is sent to the class of its base change `T ×_C U`
(`AlgebraicGeometry.Scheme.EtaleTorsor.restrictH1_classH1`). -/
noncomputable def restrictH1 :
    Sheaf.H ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1 →+
    Sheaf.H ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1 :=
  AddMonoidHom.mk' (fun x ↦ classH1 M U ⟦((classH1Equiv M C).symm x).out.pullback j⟧) fun x y ↦ by
    let s := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
    obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
    obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ j)
    apply (sheafHEquivContinuousMonoidHom M s G).injective
    rw [sheafHEquivContinuousMonoidHom_add, sheafHEquivContinuousMonoidHom_classH1,
      sheafHEquivContinuousMonoidHom_classH1, sheafHEquivContinuousMonoidHom_classH1]
    refine ContinuousMonoidHom.ext fun g ↦ ?_
    rw [ContinuousMonoidHom.mul_apply, monodromy_pullback j s _ G G', monodromy_pullback j s _ G G',
      monodromy_pullback j s _ G G', monodromy_out, monodromy_out, monodromy_out,
      sheafHEquivContinuousMonoidHom_add, ContinuousMonoidHom.mul_apply]

lemma restrictH1_apply
    (x : Sheaf.H ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    restrictH1 M j x = classH1 M U ⟦((classH1Equiv M C).symm x).out.pullback j⟧ :=
  rfl

lemma restrictH1_classH1 (T : EtaleTorsor M C) :
    restrictH1 M j (classH1 M C ⟦T⟧) = classH1 M U ⟦T.pullback j⟧ := by
  have h : ((classH1Equiv M C).symm (classH1 M C ⟦T⟧)).out.IsIsomorphic T := by
    rw [← classH1_eq_classH1_iff, classH1_out]
  exact classH1_eq_classH1_iff.2 (h.pullback j)

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the restriction maps are compatible with
the maps `H¹(-, M) → H¹(-, M')` induced by a homomorphism of coefficients `φ : M →+ M'`, for
instance the reduction `ℤ / ℓⁿ⁺¹ → ℤ / ℓⁿ`. -/
theorem restrictH1_map {M' : Type (u + 1)} [AddCommGroup M'] [Finite M'] [TopologicalSpace M']
    [DiscreteTopology M'] (φ : M →+ M')
    (x : Sheaf.H ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    restrictH1 M' j (Sheaf.H.map ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (AddCommGrpCat.ofHom φ)) 1 x) =
      Sheaf.H.map ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.ofHom φ)) 1 (restrictH1 M j x) := by
  let s := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ j)
  apply (sheafHEquivContinuousMonoidHom M' s G).injective
  refine ContinuousMonoidHom.ext fun g ↦ Multiplicative.toAdd.injective ?_
  rw [sheafHEquivContinuousMonoidHom_map]
  rw [restrictH1_apply, restrictH1_apply, sheafHEquivContinuousMonoidHom_classH1,
    sheafHEquivContinuousMonoidHom_classH1]
  rw [monodromy_pullback j s _ G G', monodromy_pullback j s _ G G', monodromy_out, monodromy_out,
    sheafHEquivContinuousMonoidHom_map]

variable [IsLocallyNoetherian C] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) (N : ℕ) [NeZero N]
  [NeZero (N : k)] [HasEnoughRootsOfUnity k N]

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the residue map
`res : H¹(U, ℤ / N) → ⊕_{z ∈ C ∖ U} Hom(μ_N(k), ℤ / N)` of the residue sequence, in the torsor
model of `H¹`: the class of a torsor `T` is sent to its residues at the boundary points
(`AlgebraicGeometry.Scheme.EtaleTorsor.residueH1_classH1`). Here `Hom(μ_N(k), ℤ / N)` is the
Tate twist `ℤ / N (-1) = H⁰(z, ℤ / N (-1))`. -/
noncomputable def residueH1 :
    Sheaf.H ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N)))) 1 →+
    ((z : ↥(Set.range j.base)ᶜ) → Additive (rootsOfUnity N k) →+ ZMod N) :=
  AddMonoidHom.mk' (fun x z ↦ ((classH1Equiv _ U).symm x).out.residue j p z.1) fun x y ↦ by
    let s := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
    obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
    let τ : fiber (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _) ≅ fiber s :=
      Iso.refl _
    funext z
    refine residue_eq_add_of_galoisCharacter_eq_add j p (fun σ ↦ ?_) z.1
    rw [galoisCharacter_eq_monodromy j _ τ G, galoisCharacter_eq_monodromy j _ τ G,
      galoisCharacter_eq_monodromy j _ τ G, monodromy_out, monodromy_out, monodromy_out,
      sheafHEquivContinuousMonoidHom_add, ContinuousMonoidHom.mul_apply, toAdd_mul,
      ULift.add_down]

omit [ConnectedSpace C] in
lemma residueH1_classH1 (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U)
    (z : ↥(Set.range j.base)ᶜ) :
    residueH1 j p N (classH1 _ U ⟦T⟧) z = T.residue j p z.1 := by
  have h : ((classH1Equiv _ U).symm (classH1 _ U ⟦T⟧)).out.IsIsomorphic T := by
    rw [← classH1_eq_classH1_iff, classH1_out]
  exact congrFun (residue_eq_of_isIsomorphic j p h) z.1

omit [ConnectedSpace C] in
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the residue maps are compatible with the
reduction of coefficients `ℤ / N d → ℤ / N`, along the transition map
`Hom(μ_{N d}, ℤ / N d) → Hom(μ_N, ℤ / N)` induced by `ξ ↦ ξ ^ d`. -/
theorem residueH1_map_castHom {d : ℕ} [NeZero (N * d)] [NeZero ((N * d : ℕ) : k)]
    [HasEnoughRootsOfUnity k (N * d)]
    (x : Sheaf.H ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod (N * d))))) 1)
    (z : ↥(Set.range j.base)ᶜ) (ξ : rootsOfUnity (N * d) k) (ξ' : rootsOfUnity N k)
    (hξ : ((ξ' : kˣ) : k) = ((ξ : kˣ) : k) ^ d) :
    residueH1 j p N (Sheaf.H.map ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      (AddCommGrpCat.ofHom (ZMod.castHom (dvd_mul_right N d) (ZMod N)).toAddMonoidHom.uliftMap))
        1 x) z (Additive.ofMul ξ') =
      ZMod.castHom (dvd_mul_right N d) (ZMod N) (residueH1 j p (N * d) x z (Additive.ofMul ξ)) := by
  let s := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  let τ : fiber (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _) ≅ fiber s := Iso.refl _
  refine residue_eq_castHom_of_galoisCharacter j p (fun σ ↦ ?_) z.1 ξ ξ' hξ
  rw [galoisCharacter_eq_monodromy j _ τ G, galoisCharacter_eq_monodromy j _ τ G, monodromy_out,
    monodromy_out, sheafHEquivContinuousMonoidHom_map]
  rfl
end H1

section Curve

open WeilGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {C U : Scheme.{u}} {p : C ⟶ Spec (.of k)}
  [IsCurve p] [SmoothOfRelativeDimension 1 p] [ConnectedSpace C] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] [IsIntegral C] [IsLocallyNoetherian C]

local notation "Ω" => SeparableClosure (Scheme.functionField C)


-- instance search through `SeparableClosure` and its integral closures is slow
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: exactness of the residue sequence at one
boundary point.

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k`, `V ⊆ C` an open with `V ∖ U = {z}`, and `N` invertible in `k`. The residue at `z` of a
`ℤ / N`-torsor `T` on `U` vanishes if and only if the monodromy of `T` is trivial on the kernel
of `π₁(U) → π₁(V)`, i.e. if and only if `T` extends over `z`. -/
theorem residue_eq_zero_iff_forall_monodromy_eq_one (V : C.Opens)
    (hV : Set.range j.base ⊆ V) (z : C) (hz : (V : Set C) \ Set.range j.base = {z})
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω') ⟶ U)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    {N : ℕ} [NeZero N] [NeZero (N : k)] (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) :
    T.residue j p z = 0 ↔ ∀ g ∈ fixingSubgroup s (IsOpenImmersion.lift V.ι j
      (by rwa [Scheme.Opens.range_ι])) G, T.monodromy s G g = 1 := by
  classical
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  obtain ⟨u₀⟩ := (inferInstance : Nonempty U)
  -- `V = U ∪ {z}`
  have hzV : z ∈ (V : Set C) \ Set.range j.base := hz ▸ rfl
  have hzj : z ∉ Set.range j.base := hzV.2
  have hVb : V = boundaryOpen (p := p) j z := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_boundaryOpen_iff]
    constructor
    · intro hx
      by_cases hxj : x ∈ Set.range j.base
      · exact Or.inl hxj
      · exact Or.inr (by simpa [hz] using (show x ∈ (V : Set C) \ Set.range j.base from ⟨hx, hxj⟩))
    · rintro (hx | rfl)
      · exact hV hx
      · exact hzV.1
  subst hVb
  have := connectedSpace_boundaryOpen (p := p) j z
  -- a chart at `z` and a point `Q` over it
  obtain ⟨c⟩ := nonempty_boundaryChart (p := p) j hzj
  have := c.isMaximal_ideal
  have := isDedekindDomain_of_isAffineOpen p c.isAffineOpen
  have : IsAlgClosed c.ideal.ResidueField := c.isAlgClosed_residueField hzj
  let τ : fiber (pointOfAlgebra Ω (genericPointLift j)) ≅ fiber s :=
    (nonempty_iso_of_fiberFunctor _ _).some
  let ρ := galoisToFundamentalGroup (genericPointLift j) τ G
  have hχ (σ : Gal(Ω/C.functionField)) :
      T.galoisCharacter j σ = (T.monodromy s G (ρ σ)).toAdd.down :=
    galoisCharacter_eq_monodromy j T τ G σ
  -- the image of inertia acts trivially on the covers extending over `z`
  have hIloc : ∀ σ ∈ c.point.inertia Gal(Ω/C.functionField),
      ρ σ ∈ fixingSubgroup s (toOpen j (boundaryOpen (p := p) j z)
        (opensRange_le_boundaryOpen j z)) G := by
    intro σ hσ P x
    obtain ⟨t, rfl⟩ : ∃ t, τ.hom.app _ t = x :=
      ⟨τ.inv.app _ x, ConcreteCategory.congr_hom (τ.inv_hom_id_app _) x⟩
    rw [galoisToFundamentalGroup_smul]
    congr 1
    exact galoisToAut_hom_app_pullback_eq_of_mem_inertia j c.isAffineOpen c.point
      (boundaryOpen (p := p) j z) (opensRange_le_boundaryOpen j z) c.le hσ P t
  have hN : (N : k) ≠ 0 := NeZero.ne _
  constructor
  · intro h0 g hg
    -- a Kummer element against a primitive root of unity
    obtain ⟨ζk, hζk⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k N
    let ζ : Ω := algebraMap C.functionField Ω (p.functionFieldConstants ζk)
    have hζ : IsPrimitiveRoot ζ N :=
      hζk.map_of_injective ((algebraMap C.functionField Ω).comp p.functionFieldConstants).injective
    obtain ⟨x, f, hx0, hf, hxσ⟩ := T.exists_kummerElement j p hζk.pow_eq_one
    have hf0 := ne_zero_of_algebraMap_eq_pow hx0 hf
    have hres := T.residue_eq_ord j p z (Additive.ofMul hζk.toRootsOfUnity) hx0 hf hxσ
    rw [h0] at hres
    have hdvd : (N : ℤ) ∣ C.ord f z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by rw [← hres]; rfl)
    -- inertia fixes the Kummer element, so the monodromy is trivial on inertia
    have hI : ∀ σ ∈ c.point.inertia Gal(Ω/C.functionField), T.monodromy s G (ρ σ) = 1 := by
      intro σ hσ
      have hfix : σ x = x := c.inertia_apply_eq_of_dvd_ord hzj c.point hσ hN hf0 hf hdvd
      rw [hxσ σ] at hfix
      have h1 : ζ ^ (T.galoisCharacter j σ).val = 1 := by
        have := mul_right_cancel₀ hx0 (hfix.trans (one_mul x).symm)
        exact this
      have h2 : T.galoisCharacter j σ = 0 := by
        rw [← ZMod.natCast_zmod_val (T.galoisCharacter j σ), ZMod.natCast_eq_zero_iff]
        exact hζ.pow_eq_one_iff_dvd _ |>.1 h1
      rw [hχ] at h2
      apply Multiplicative.toAdd.injective
      exact ULift.ext h2
    -- the kernel of the monodromy is a closed normal subgroup containing the image of inertia
    let K := (T.monodromy s G).toMonoidHom.ker
    have hKc : IsClosed (K : Set G) :=
      (isClosed_discrete {(1 : Multiplicative (ULift.{u + 1} (ZMod N)))}).preimage
        (T.monodromy s G).continuous
    have hsub : ((c.point.inertia Gal(Ω/C.functionField)).map ρ : Set G) ⊆ K := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact hI σ hσ
    have hker := c.fixingSubgroup_le_topologicalClosure_normalClosure hzj c.point s G τ hg
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hKc hker
  · intro h
    refine AddMonoidHom.ext fun ξ ↦ ?_
    have hξ : ((ξ.toMul : kˣ) : k) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N _).1 ξ.toMul.2, Units.val_one]
    obtain ⟨x, f, hx0, hf, hxσ⟩ := T.exists_kummerElement j p hξ
    rw [T.residue_eq_ord j p z ξ hx0 hf hxσ, AddMonoidHom.zero_apply]
    -- inertia fixes the Kummer element
    have hI : ∀ σ ∈ c.point.inertia Gal(Ω/C.functionField), σ x = x := by
      intro σ hσ
      have h1 := h _ (hIloc σ hσ)
      rw [hxσ σ, hχ, h1]
      simp
    have hdvd := c.dvd_ord_of_forall_inertia hzj c.point hx0 hf hI
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hdvd

omit [IsCurve p] [SmoothOfRelativeDimension 1 p] [ConnectedSpace C] [IsIntegral C]
  [IsLocallyNoetherian C] [IsOpenImmersion j] [Nonempty U] in
/-- The monodromy of the base change of a torsor along `f` is trivial on the kernel of
`π₁(U) → π₁(Y)`. -/
lemma monodromy_pullback_eq_one_of_mem_fixingSubgroup {M : Type (u + 1)} [AddCommGroup M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] {Y : Scheme.{u}} (f : U ⟶ Y)
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω') ⟶ U)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (T : EtaleTorsor M Y) {g : G} (hg : g ∈ fixingSubgroup s f G) :
    (T.pullback f).monodromy s G g = 1 := by
  obtain ⟨y⟩ := (T.pullback f).nonempty_fiber s
  exact ((T.pullback f).monodromy_eq_iff s G g y 0).mpr
    (by rw [fiber_map_vaddHom_zero]; exact (hg T.toFiniteEtale y).symm)

omit [IsCurve p] [SmoothOfRelativeDimension 1 p] in
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: injectivity of `H¹(C, M) → H¹(U, M)`.

Torsors on a connected regular locally noetherian scheme `C` (for instance a smooth connected
curve over a field) whose restrictions to a nonempty open `U` are isomorphic are isomorphic. -/
theorem isIsomorphic_of_isIsomorphic_pullback_of_isRegular [IsRegular C] {M : Type (u + 1)}
    [AddCommGroup M] [Finite M] {T₁ T₂ : EtaleTorsor M C}
    (h : (T₁.pullback j).IsIsomorphic (T₂.pullback j)) :
    T₁.IsIsomorphic T₂ := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let s := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ j)
  exact isIsomorphic_of_isIsomorphic_pullback j s
    (fundamentalGroupMap_surjective_of_isRegular j (pullbackFiberIso j s) G G') h

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: exactness of the residue sequence
`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → ⊕_{z ∈ C ∖ U} ℤ / N (-1)` in the middle.

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k`, and `N` invertible in `k`. A `ℤ / N`-torsor on `U` is the restriction of a torsor on `C` if
and only if its residues at all the boundary points vanish. -/
theorem exists_isIsomorphic_pullback_iff_residue_eq_zero {N : ℕ} [NeZero N] [NeZero (N : k)]
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) :
    (∃ T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) C, (T'.pullback j).IsIsomorphic T) ↔
      ∀ z ∉ Set.range j.base, T.residue j p z = 0 := by
  classical
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsRegular C := IsRegular.of_smooth p
  have := irreducibleSpace_of_smooth (p := p)
  let s := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  -- the open `U ∪ {z}` for a boundary point `z`
  have hVz (z : C) (hz : z ∉ Set.range j.base) :
      ((boundaryOpen (p := p) j z : C.Opens) : Set C) \ Set.range j.base = {z} := by
    ext x
    simp only [Set.mem_sdiff, SetLike.mem_coe, mem_boundaryOpen_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h₁ | h₁, h₂⟩
      · exact absurd h₁ h₂
      · exact h₁
    · rintro rfl
      exact ⟨Or.inr rfl, hz⟩
  have hres (z : C) (hz : z ∉ Set.range j.base) :=
    residue_eq_zero_iff_forall_monodromy_eq_one (p := p) (boundaryOpen (p := p) j z)
      (fun x hx ↦ (mem_boundaryOpen_iff j).2 (Or.inl hx)) z (hVz z hz) s G (N := N) T
  constructor
  · rintro ⟨T', hT'⟩ z hz
    refine (hres z hz).2 fun g hg ↦ ?_
    have hg' := fixingSubgroup_le_comp s _ G (boundaryOpen (p := p) j z).ι hg
    rw [IsOpenImmersion.lift_fac] at hg'
    rw [← monodromy_eq_of_isIsomorphic s G hT']
    exact monodromy_pullback_eq_one_of_mem_fixingSubgroup j s G T' hg'
  · intro h
    -- the monodromy of `T` kills the kernel of `π₁(U) → π₁(C)`
    let S := boundaryFinset (p := p) j
    have hS := isClosed_of_mem_boundaryFinset (p := p) j
    have hSU := (coe_boundaryFinset (p := p) j).symm
    have hV : ∀ z ∈ S, ConnectedSpace (complOpens S hS {z}).toScheme := fun z hz ↦ by
      obtain ⟨u⟩ := (inferInstance : Nonempty U)
      have hne : ((complOpens S hS {z} : C.Opens) : Set C).Nonempty :=
        ⟨j u, range_le_complOpens j S hS hSU {z} ⟨u, rfl⟩⟩
      have hirr : IsIrreducible ((complOpens S hS {z} : C.Opens) : Set C) :=
        ⟨hne, (IrreducibleSpace.isIrreducible_univ C).isPreirreducible.open_subset
          (complOpens S hS {z}).isOpen (Set.subset_univ _)⟩
      exact isConnected_iff_connectedSpace.1 hirr.isConnected
    have hconn : ∀ z ∈ S, ∀ P : (complOpens S hS {z}).toScheme.FiniteEtale, IsConnected P →
        IsConnected ((FiniteEtale.pullback (toComplOpens j S hS hSU {z})).obj P) :=
        fun z hz P hP ↦ by
      have := hV z hz
      have := connectedSpace_of_isConnected P
      have : Etale P.obj.hom := P.obj.prop
      let q : P.obj.left ⟶ Spec (.of k) := P.obj.hom ≫ (complOpens S hS {z}).ι ≫ p
      have : Smooth q := inferInstance
      have := LocallyOfFiniteType.isLocallyNoetherian q
      have := IsRegular.of_smooth q
      have := IsRegular.irreducibleSpace P.obj.left
      exact isConnected_pullback_of_irreducibleSpace _ P
    have hkill : ∀ g ∈ fixingSubgroup s j G, T.monodromy s G g = 1 := by
      let K := (T.monodromy s G).toMonoidHom.ker
      have hKc : IsClosed (K : Set G) :=
        (isClosed_discrete {(1 : Multiplicative (ULift.{u + 1} (ZMod N)))}).preimage
          (T.monodromy s G).continuous
      have hle : (⨆ z : S, fixingSubgroup s (toComplOpens j S hS hSU {z.1}) G) ≤ K :=
        iSup_le fun z g hg ↦ by
          have hz : z.1 ∉ Set.range j.base := by
            change z.1 ∈ (Set.range j.base)ᶜ
            rw [hSU]
            exact z.2
          exact (hres z.1 hz).1 (h z.1 hz) g hg
      intro g hg
      exact Subgroup.topologicalClosure_minimal _ hle hKc
        (fixingSubgroup_le_topologicalClosure_iSup j S hS hSU s G hV hconn hg)
    -- so `T` comes from `C`
    obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ j)
    exact exists_isIsomorphic_pullback j s
      (fundamentalGroupMap_surjective_of_isRegular j (pullbackFiberIso j s) G G') T hkill

omit [IsCurve p] [SmoothOfRelativeDimension 1 p] in
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: exactness of the residue sequence
`0 → H¹(C, M) → H¹(U, M)` on the left: the restriction map is injective, for `C` connected,
regular and locally noetherian (for instance a smooth connected curve over a field). -/
theorem injective_restrictH1 [IsRegular C] {M : Type (u + 1)} [AddCommGroup M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] : Function.Injective (restrictH1 M j) := by
  intro x y h
  obtain ⟨T₁, rfl⟩ := (bijective_classH1 (M := M) (Y := C)).2 x
  obtain ⟨T₂, rfl⟩ := (bijective_classH1 (M := M) (Y := C)).2 y
  induction T₁ using Quotient.inductionOn with | h t₁ => ?_
  induction T₂ using Quotient.inductionOn with | h t₂ => ?_
  rw [restrictH1_classH1, restrictH1_classH1, classH1_eq_classH1_iff] at h
  exact classH1_eq_classH1_iff.2 (isIsomorphic_of_isIsomorphic_pullback_of_isRegular h)

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: exactness of the residue sequence (5.1)

`0 → H¹(C, ℤ / N) → H¹(U, ℤ / N) → ⊕_{z ∈ C ∖ U} ℤ / N (-1)`

in the middle: the image of the restriction map is the kernel of the residue map. Here `U` is a
nonempty open of a smooth connected curve `C` over an algebraically closed field `k`, `N` is
invertible in `k` and `ℤ / N (-1) = Hom(μ_N(k), ℤ / N)`. -/
theorem range_restrictH1_eq_ker_residueH1 (N : ℕ) [NeZero N] [NeZero (N : k)] :
    (restrictH1 (ULift.{u + 1} (ZMod N)) j).range = (residueH1 j p N).ker := by
  ext x
  obtain ⟨T, rfl⟩ := (bijective_classH1 (M := ULift.{u + 1} (ZMod N)) (Y := U)).2 x
  induction T using Quotient.inductionOn with | h t => ?_
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  trans ∃ T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) C, (T'.pullback j).IsIsomorphic t
  · constructor
    · rintro ⟨y, hy⟩
      obtain ⟨T', rfl⟩ := (bijective_classH1 (M := ULift.{u + 1} (ZMod N)) (Y := C)).2 y
      induction T' using Quotient.inductionOn with | h t' => ?_
      rw [restrictH1_classH1, classH1_eq_classH1_iff] at hy
      exact ⟨t', hy⟩
    · rintro ⟨t', h⟩
      exact ⟨classH1 _ C ⟦t'⟧, by rw [restrictH1_classH1, classH1_eq_classH1_iff]; exact h⟩
  rw [exists_isIsomorphic_pullback_iff_residue_eq_zero (p := p)]
  constructor
  · intro h
    funext z
    rw [residueH1_classH1]
    exact h z.1 z.2
  · intro h z hz
    have := congrFun h ⟨z, hz⟩
    rwa [residueH1_classH1] at this

end Curve

end AlgebraicGeometry.Scheme.EtaleTorsor
