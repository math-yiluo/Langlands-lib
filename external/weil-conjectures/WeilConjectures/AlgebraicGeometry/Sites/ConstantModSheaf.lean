/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapComp

/-!
# Constant sheaves of `𝔽_p`-vector spaces and the constant sheaf `ℤ/p`

Let `p` be a prime and `M` an abelian group killed by `p`, for instance `M = Λ/pΛ` for a
commutative ring `Λ`. Then `M` is an `𝔽_p`-vector space, hence a direct sum of copies of `𝔽_p`,
and the constant étale sheaf `M_X` on a scheme `X` is the filtered colimit of finite direct sums
of copies of the constant sheaf `ℤ/p` (`AlgebraicGeometry.Scheme.constantZMod`); if `M` is
finite, it is itself such a finite direct sum. We record the resulting transfer principle
`AlgebraicGeometry.Scheme.constantSheaf_induction_of_nsmul_eq_zero` and apply it to the
cohomology of `M_X`: on a quasi-compact quasi-separated scheme, vanishing, finiteness and
the bijectivity of pullback maps pass from `ℤ/p` to `M_X`, the cohomology commuting with
finite direct sums and with filtered colimits
(`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`).

## Main statements

- `AlgebraicGeometry.Etale.constantModSheafForgetIso`: the underlying abelian sheaf of the
  constant sheaf `Λ/dΛ` of `Λ`-modules is the constant abelian sheaf `Λ/dΛ`.
- `AlgebraicGeometry.Scheme.constantSheaf_induction_of_nsmul_eq_zero`,
  `AlgebraicGeometry.Scheme.constantSheaf_induction_of_finite`: the transfer principle.
- `AlgebraicGeometry.Etale.subsingleton_sheafH_constantModSheaf`,
  `AlgebraicGeometry.Etale.finite_sheafH_constantModSheaf`,
  `AlgebraicGeometry.Etale.bijective_cohomologyMap_constantModSheaf`: vanishing, finiteness
  and bijectivity of pullback maps for the constant sheaf `Λ/pΛ`, deduced from `ℤ/p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Finite direct sums and filtered colimits -/

namespace Etale

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (q : ℕ)

/-- The pullback map on étale cohomology is bijective for a finite direct sum of sheaves if it
is bijective for each summand. -/
theorem bijective_cohomologyMap_biproduct
    [HasFiniteBiproducts (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ)
    (G : Fin n → Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ i, Function.Bijective (cohomologyMap g (G i) q)) :
    Function.Bijective (cohomologyMap g (⨁ G) q) := by
  classical
  let H := Sheaf.functorH Y.smallEtaleTopology q
  let H' := Sheaf.functorH X.smallEtaleTopology q
  let P := (g)^*[AddCommGrpCat.{u + 1}]
  have hH {A B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : A ⟶ B)
      (x : Sheaf.H A q) : Sheaf.H.map φ q x = H.map φ x := rfl
  have hH' {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : A ⟶ B)
      (x : Sheaf.H A q) : Sheaf.H.map φ q x = H'.map φ x := rfl
  have htot : ∑ i, biproduct.π G i ≫ biproduct.ι G i = 𝟙 (⨁ G) := biproduct.total
  have hsum {A B : AddCommGrpCat.{u + 1}} (f : Fin n → (A ⟶ B)) (x : A) :
      (∑ i, f i) x = ∑ i, f i x :=
    map_sum (⟨⟨fun φ ↦ φ x, rfl⟩, fun _ _ ↦ rfl⟩ : (A ⟶ B) →+ B) f _
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero] at hxy ⊢
    rw [← map_sub] at hxy
    set z := x - y
    have hz (i : Fin n) : Sheaf.H.map (biproduct.π G i) q z = 0 := by
      apply (hG i).1
      rw [cohomologyMap_map, hxy, map_zero, map_zero]
    rw [← Sheaf.H.map_id_apply (F := ⨁ G) z, ← htot, hH, H.map_sum,
      hsum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← hH, Sheaf.H.map_comp_apply, hz, map_zero]
  · choose x hx using fun i ↦ (hG i).2 (Sheaf.H.map (P.map (biproduct.π G i)) q y)
    refine ⟨∑ i, Sheaf.H.map (biproduct.ι G i) q (x i), ?_⟩
    rw [map_sum]
    conv_rhs => rw [← Sheaf.H.map_id_apply (F := P.obj (⨁ G)) y, ← P.map_id, ← htot,
      P.map_sum, hH', H'.map_sum, hsum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [cohomologyMap_map, hx, ← hH', ← Sheaf.H.map_comp_apply, ← P.map_comp]

/-- The pullback map on étale cohomology along `g : X ⟶ Y` between quasi-compact
quasi-separated schemes is bijective for a filtered colimit of sheaves if it is bijective for
each member of the diagram: cohomology commutes with filtered colimits
(`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`) and `g^*` preserves colimits. -/
theorem bijective_cohomologyMap_of_isColimit' [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {J : Type*} [Category J] [IsFiltered J]
    {D : J ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (hD : ∀ j, Function.Bijective (cohomologyMap g (D.obj j) q)) :
    Function.Bijective (cohomologyMap g c.pt q) := by
  let P := (g)^*[AddCommGrpCat.{u + 1}]
  have : PreservesColimitsOfShape J P :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).leftAdjoint_preservesColimits.1
  have hc' : IsColimit (P.mapCocone c) := isColimitOfPreserves P hc
  obtain ⟨hs, hi⟩ := Scheme.H_map_isColimit_of_isFiltered Y hc q
  obtain ⟨hs', hi'⟩ := Scheme.H_map_isColimit_of_isFiltered X hc' q
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨j, y, rfl⟩ := hs x
    rw [show cohomologyMap g c.pt q (Sheaf.H.map (c.ι.app j) q y) =
      Sheaf.H.map (P.map (c.ι.app j)) q (cohomologyMap g (D.obj j) q y) from
        cohomologyMap_map g q (c.ι.app j) y] at hx
    obtain ⟨j', φ, hφ⟩ := hi' j _ hx
    have : Sheaf.H.map (D.map φ) q y = 0 := by
      apply (injective_iff_map_eq_zero _).1 (hD j').1
      rw [cohomologyMap_map]
      exact hφ
    rw [← c.w φ, Sheaf.H.map_comp_apply, this, map_zero]
  · obtain ⟨j, w, rfl⟩ := hs' z
    obtain ⟨y, rfl⟩ := (hD j).2 w
    exact ⟨Sheaf.H.map (c.ι.app j) q y, cohomologyMap_map g q _ y⟩

end Etale

/-- Étale cohomology on a quasi-compact quasi-separated scheme of a filtered colimit of sheaves
without cohomology in degree `q` has no cohomology in degree `q`. -/
theorem Scheme.subsingleton_H_of_isColimit_of_isFiltered (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {J : Type*} [Category J] [IsFiltered J]
    {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) (hD : ∀ j, Subsingleton (Sheaf.H (D.obj j) q)) :
    Subsingleton (Sheaf.H c.pt q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨j, y, rfl⟩ := (Scheme.H_map_isColimit_of_isFiltered X hc q).1 x
  rw [Subsingleton.elim y 0, map_zero]

/-! ### Constant sheaves of `𝔽_p`-vector spaces -/

section Transfer

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]

/-- The constant sheaf `ℤ/p` is the constant sheaf associated with the ring `𝔽_p`, seen as a
module over itself. -/
lemma Scheme.constantZMod_eq :
    X.constantZMod p = (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) AddCommGrpCat.{u + 1}
      ⋙ constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))) :=
  rfl

/-- The constant sheaf on a finite direct sum of copies of `𝔽_p` is a finite direct sum of
copies of `ℤ/p`. -/
lemma Scheme.nonempty_iso_biproduct_constantZMod (S : Type (u + 1)) [Finite S] :
    ∃ n : ℕ, Nonempty ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)))
      AddCommGrpCat.{u + 1} ⋙ constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (∐ fun _ : S ↦ ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))) ≅
      ⨁ fun _ : Fin n ↦ X.constantZMod p) := by
  let := Fintype.ofFinite S
  let T := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p))) AddCommGrpCat.{u + 1} ⋙
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let a : S → ModuleCat.{u + 1} (ULift.{u + 1} (ZMod p)) :=
    fun _ ↦ ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))
  exact ⟨Fintype.card S, ⟨PreservesCoproduct.iso T a ≪≫
    (biproduct.isoCoproduct (fun _ : S ↦ X.constantZMod p)).symm ≪≫
    biproduct.whiskerEquiv (f := fun _ : S ↦ X.constantZMod p)
      (g := fun _ : Fin (Fintype.card S) ↦ X.constantZMod p) (Fintype.equivFin S)
      (fun _ ↦ Iso.refl _)⟩⟩

variable {X p}

/-- **Transfer principle for constant sheaves of `𝔽_p`-vector spaces.** Let `P` be a property
of abelian étale sheaves on `X` which is invariant under isomorphism, holds for every finite
direct sum of copies of `ℤ/p` and is stable under filtered colimits. Then `P` holds for the
constant sheaf `M_X` of every abelian group `M` killed by `p`: `M` is an `𝔽_p`-vector space,
the filtered colimit of its finite-dimensional subspaces spanned by parts of a basis. -/
theorem Scheme.constantSheaf_induction_of_nsmul_eq_zero
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (hiso : ∀ {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}, (G ≅ G') → P G → P G')
    (hsum : ∀ n : ℕ, P (⨁ fun _ : Fin n ↦ X.constantZMod p))
    (hcolim : ∀ {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]
      {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D},
      IsColimit c → (∀ j, P (D.obj j)) → P c.pt)
    (M : Type (u + 1)) [AddCommGroup M] (hM : ∀ x : M, p • x = 0) :
    P ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) := by
  classical
  let R := ULift.{u + 1} (ZMod p)
  let : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let : Module R M := Module.compHom M ULift.ringEquiv.toRingHom
  let B := Module.Basis.ofVectorSpaceIndex R M
  let b : Module.Basis B R M := Module.Basis.ofVectorSpace R M
  let a : B → ModuleCat.{u + 1} R := fun _ ↦ ModuleCat.of R R
  let T := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let eM : (∐ a) ≅ ModuleCat.of R M :=
    (colimit.isColimit (Discrete.functor a)).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit R R B) ≪≫ b.repr.symm.toModuleIso
  have hc := isColimitOfPreserves T
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone a)
  refine hiso (T.mapIso eM) (hcolim hc fun S ↦ ?_)
  obtain ⟨n, ⟨e⟩⟩ := Scheme.nonempty_iso_biproduct_constantZMod X p S
  exact hiso e.symm (hsum n)

/-- **Transfer principle for constant sheaves of finite `𝔽_p`-vector spaces.** Let `P` be a
property of abelian étale sheaves on `X` which is invariant under isomorphism and holds for
every finite direct sum of copies of `ℤ/p`. Then `P` holds for the constant sheaf `M_X` of every
finite abelian group `M` killed by `p`. -/
theorem Scheme.constantSheaf_induction_of_finite
    (P : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (hiso : ∀ {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}, (G ≅ G') → P G → P G')
    (hsum : ∀ n : ℕ, P (⨁ fun _ : Fin n ↦ X.constantZMod p))
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] (hM : ∀ x : M, p • x = 0) :
    P ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) := by
  classical
  let R := ULift.{u + 1} (ZMod p)
  let : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let : Module R M := Module.compHom M ULift.ringEquiv.toRingHom
  let B := Module.Basis.ofVectorSpaceIndex R M
  let b : Module.Basis B R M := Module.Basis.ofVectorSpace R M
  have : Finite B := Finite.of_injective b b.injective
  let a : B → ModuleCat.{u + 1} R := fun _ ↦ ModuleCat.of R R
  let T := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let eM : (∐ a) ≅ ModuleCat.of R M :=
    (colimit.isColimit (Discrete.functor a)).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit R R B) ≪≫ b.repr.symm.toModuleIso
  obtain ⟨n, ⟨e⟩⟩ := Scheme.nonempty_iso_biproduct_constantZMod X p B
  exact hiso (e.symm ≪≫ T.mapIso eM) (hsum n)

end Transfer

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The underlying abelian sheaf of the constant sheaf `Λ/dΛ` of `Λ`-modules is the constant
abelian sheaf `Λ/dΛ`. -/
noncomputable def constantModSheafForgetIso (X : Scheme.{u}) (d : ℕ) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (constantModSheaf Λ X d) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ))) :=
  have : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    apply GrothendieckTopology.instPreservesSheafification
  (constantCommuteCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app
      (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)))

/-- Every element of `Λ/dΛ` is killed by `d`. -/
lemma nsmul_quotient_span_eq_zero (d : ℕ) (x : Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)) :
    d • x = 0 := by
  have hd : ((d : Λ) : Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (d : Λ))
  rw [nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk _), hd, zero_mul]

variable {X : Scheme.{u}} (p : ℕ) [Fact p.Prime] (q : ℕ)

/-- **Vanishing for `Λ/pΛ` from `ℤ/p`.** On a quasi-compact quasi-separated scheme `X`, if
`Hᵠ(X, ℤ/p) = 0`, then `Hᵠ(X, Λ/pΛ) = 0`. -/
theorem subsingleton_sheafH_constantModSheaf [CompactSpace X] [QuasiSeparatedSpace X]
    (h : Subsingleton (Sheaf.H (X.constantZMod p) q)) :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj (constantModSheaf Λ X p)) q) := by
  have := h
  have key := Scheme.constantSheaf_induction_of_nsmul_eq_zero (X := X) (p := p)
    (fun G ↦ Subsingleton (Sheaf.H G q))
    (fun e hG ↦ (Sheaf.H.map_bijective_of_iso e.symm q).1.subsingleton)
    (fun n ↦ (Abelian.Ext.addEquivBiproduct _
      (biproduct.isBilimit fun _ : Fin n ↦ X.constantZMod p) q).toEquiv.subsingleton)
    (fun hc hD ↦ Scheme.subsingleton_H_of_isColimit_of_isFiltered X hc q hD)
    _ (nsmul_quotient_span_eq_zero Λ p)
  exact (Sheaf.H.map_bijective_of_iso (constantModSheafForgetIso Λ X p) q).1.subsingleton

/-- **Finiteness for `Λ/pΛ` from `ℤ/p`.** If `Λ/pΛ` and `Hᵠ(X, ℤ/p)` are finite, then so is
`Hᵠ(X, Λ/pΛ)`. -/
theorem finite_sheafH_constantModSheaf [Finite (Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ))]
    (h : Finite (Sheaf.H (X.constantZMod p) q)) :
    Finite (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj (constantModSheaf Λ X p)) q) := by
  have := h
  have key := Scheme.constantSheaf_induction_of_finite (X := X) (p := p)
    (fun G ↦ Finite (Sheaf.H G q))
    (fun e hG ↦ Finite.of_injective _ (Sheaf.H.map_bijective_of_iso e.symm q).1)
    (fun n ↦ Finite.of_equiv _ (Abelian.Ext.addEquivBiproduct _
      (biproduct.isBilimit fun _ : Fin n ↦ X.constantZMod p) q).toEquiv.symm)
    _ (nsmul_quotient_span_eq_zero Λ p)
  exact Finite.of_injective _ (Sheaf.H.map_bijective_of_iso (constantModSheafForgetIso Λ X p) q).1

/-- **Bijectivity of pullback maps for `Λ/pΛ` from `ℤ/p`.** Let `g : X' ⟶ X` be a morphism of
quasi-compact quasi-separated schemes. If the pullback map `Hᵠ(X, ℤ/p) ⟶ Hᵠ(X', g^* ℤ/p)` is
bijective, then so is `Hᵠ(X, Λ/pΛ) ⟶ Hᵠ(X', g^* Λ/pΛ)`. -/
theorem bijective_cohomologyMap_constantModSheaf {X' : Scheme.{u}} (g : X' ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    (h : Function.Bijective (cohomologyMap g (X.constantZMod p) q)) :
    Function.Bijective (cohomologyMap g ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj (constantModSheaf Λ X p)) q) := by
  have key := Scheme.constantSheaf_induction_of_nsmul_eq_zero (X := X) (p := p)
    (fun G ↦ Function.Bijective (cohomologyMap g G q))
    (fun e hG ↦ (bijective_cohomologyMap_iff_of_iso g e q).1 hG)
    (fun n ↦ have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      HasFiniteBiproducts.of_hasFiniteProducts
      bijective_cohomologyMap_biproduct g q n _ fun _ ↦ h)
    (fun hc hD ↦ bijective_cohomologyMap_of_isColimit' g q hc hD)
    _ (nsmul_quotient_span_eq_zero Λ p)
  exact (bijective_cohomologyMap_iff_of_iso g (constantModSheafForgetIso Λ X p).symm q).1 key

end Etale

end AlgebraicGeometry
