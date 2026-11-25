/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.UniformMittagLeffler
public import WeilConjectures.CategoryTheory.Abelian.AdicImageTower

/-!
# Exact `ℓ`-adic towers from uniformly Artin-Rees towers of étale sheaves

Let `X` be a scheme and `(Hₙ)` a tower of étale sheaves of `Λ`-modules on `X` which is
**uniformly Artin-Rees** with constant `c` (`AlgebraicGeometry.Etale.IsArtinReesTower`): at every
geometric point `s`, with `L_s` the limit of the tower of stalks `((Hₙ)_s)ₙ`, the kernel of
`L_s ⟶ (Hₘ)_s` is `ℓᵐ L_s`, the image of `(Hₘ₊꜀)_s ⟶ (Hₘ)_s` is contained in that of `L_s`, and
`ℓᶜ` kills the `ℓ`-power torsion of `L_s`. This is the situation of the higher direct images
`Hₙ = Rʲf_* Gₙ` of an `ℓ`-adic tower along a smooth proper morphism.

Then the `ℓ`-adic image tower `G'ₘ = ℓᶜ · im(H_{m+2c} ⟶ H_{m+c}) ⊆ H_{m+c}`
(`CategoryTheory.Functor.adicImageTower`) is an exact `ℓ`-adic tower:

- its transition maps `G'ₖ ⟶ G'ₙ` are cokernels of `ℓⁿ`
  (`AlgebraicGeometry.Etale.IsArtinReesTower.isColimitCokernelCofork`) and it is flat, so that it
  carries an `ℓ`-adic tower structure
  (`AlgebraicGeometry.Etale.IsArtinReesTower.adicTowerStructure`);
- its terms are finite locally constant if the `Hₙ` are, `Λ` being noetherian
  (`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_adicImageTower`);
- over a discrete valuation ring `Λ` in which `ℓ` is a nonzero nonunit, the stalks of `G'ₘ` are
  `ℓᶜL_s / ℓᵐ⁺ᶜL_s ≅ (Λ / ℓᵐ)ʳ`
  (`AlgebraicGeometry.Etale.IsArtinReesTower.exists_linearEquiv_sheafFiber`).

The inclusion `G'ₘ ⟶ H_{m+c}` is a monomorphism whose cokernel is killed by `ℓ²ᶜ` as soon as
`ℓᶜ : Hₙ ⟶ Hₙ` factors through the transition map `H_{n+c} ⟶ Hₙ`
(`CategoryTheory.Functor.pow_smul_cokernel_π_adicImageTowerι_eq_zero`).

Exactness is checked on the stalks at the geometric points `X.algClosurePoint x`, which form a
conservative family (`AlgebraicGeometry.Etale.exact_of_forall_sheafFiber`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The stalk functors of étale sheaves of modules are additive. -/
instance {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- An étale sheaf of `Λ`-modules whose stalks at all the geometric points `X.algClosurePoint x`
vanish is zero. -/
lemma isZero_of_forall_isZero_sheafFiber_algClosurePoint
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (h : ∀ x : X, IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F)) :
    IsZero F := by
  have : IsIso (0 : F ⟶ 0) := Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦
    (NatIso.isIso_map_iff (GrothendieckTopology.Point.uliftSheafFiberIso.{u + 1}
      (pointSmallEtale (X.algClosurePoint x)) (ModuleCat.{u + 1} Λ)) _).2
      (isIso_of_source_target_iso_zero _ (h x).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

/-- **Exactness of étale sheaves is checked on stalks**: a short complex of étale sheaves of
`Λ`-modules is exact if it is exact on the stalks at all geometric points `X.algClosurePoint x`. -/
lemma exact_of_forall_sheafFiber
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : ∀ (x : X) (y : (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj S.X₂),
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map S.g y = 0 →
        ∃ z, (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map S.f z = y) :
    S.Exact := by
  rw [S.exact_iff_isZero_homology]
  exact isZero_of_forall_isZero_sheafFiber_algClosurePoint fun x ↦
    ((S.map (pointSmallEtale (X.algClosurePoint x)).sheafFiber).exact_iff_isZero_homology.1
      ((S.map (pointSmallEtale (X.algClosurePoint x)).sheafFiber).moduleCat_exact_iff.2
        (h x))).of_iso
      (S.mapHomologyIso (pointSmallEtale (X.algClosurePoint x)).sheafFiber).symm

/-- A morphism of étale sheaves of `Λ`-modules which is surjective on the stalks at all geometric
points `X.algClosurePoint x` is an epimorphism. -/
lemma epi_of_forall_surjective_sheafFiber_map
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    (h : ∀ x : X, Function.Surjective
      ((pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map φ)) :
    Epi φ :=
  (ShortComplex.exact_iff_epi (ShortComplex.mk φ (0 : G ⟶ 0) Limits.comp_zero)
    rfl).1 (exact_of_forall_sheafFiber fun x y _ ↦ h x y)

/-- On stalks, `n • 𝟙` is multiplication by `n`. -/
lemma sheafFiber_map_nsmul_id_apply {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (z : (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj F) :
    (pointSmallEtale s).sheafFiber.map (n • 𝟙 F) z = n • z := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

/-- The image of a morphism between finite locally constant sheaves of modules over a noetherian
ring is finite locally constant. -/
lemma isFiniteLocallyConstantSheaf_image [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F]
    [IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (image φ) :=
  have := IsFiniteLocallyConstantSheaf.cokernel φ
  have := IsFiniteLocallyConstantSheaf.kernel (cokernel.π φ)
  IsFiniteLocallyConstantSheaf.of_iso (Abelian.imageIsoImage φ)

variable (H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ℓ c : ℕ)

/-- The terms of the `ℓ`-adic image tower of a tower of finite locally constant sheaves of modules
over a noetherian ring are finite locally constant. -/
instance isFiniteLocallyConstantSheaf_adicImageTower [IsNoetherianRing Λ]
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (H.obj (op n))] (m : ℕ) :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) ((H.adicImageTower ℓ c).obj (op m)) :=
  isFiniteLocallyConstantSheaf_image (H.adicImageTowerMap ℓ c m)

/-- A tower `(Hₙ)` of étale sheaves of `Λ`-modules is **uniformly Artin-Rees** with constant `c`
if at every geometric point `s`, with `L_s` the limit of the tower of stalks `((Hₙ)_s)ₙ`, the
image of `(Hₘ₊꜀)_s ⟶ (Hₘ)_s` is contained in that of `L_s`, the kernel of `L_s ⟶ (Hₘ)_s` is
`ℓᵐ L_s`, and `ℓᶜ` kills the `ℓ`-power torsion of `L_s`. -/
structure IsArtinReesTower : Prop where
  exists_eval_eq {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (m : ℕ)
    (z : (H ⋙ (pointSmallEtale s).sheafFiber).obj (op (m + c))) :
    ∃ x : ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber),
      x.1 (op m) = ModuleCat.towerMap _ (Nat.le_add_right m c) z
  eval_eq_zero_iff {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (m : ℕ)
    (x : ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber)) :
    x.1 (op m) = 0 ↔ ∃ y, ℓ ^ m • y = x
  pow_smul_eq_zero {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (y : ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber)) (k : ℕ) :
    ℓ ^ k • y = 0 → ℓ ^ c • y = 0

namespace IsArtinReesTower

variable {H ℓ c} (hH : IsArtinReesTower H ℓ c)
  (hzero : ∀ n : ℕ, ℓ ^ n • 𝟙 (H.obj (op n)) = 0)

include hH in
/-- The transition maps of the `ℓ`-adic image tower are epimorphisms. -/
lemma epi_adicImageTower_map {n k : ℕ} (h : n ≤ k) :
    Epi ((H.adicImageTower ℓ c).map (homOfLE h).op) :=
  epi_of_forall_surjective_sheafFiber_map _ fun x ↦
    H.surjective_map_adicImageTower_map ℓ c _ (hH.exists_eval_eq (X.algClosurePoint x)) h

/-- **The transition maps `G'ₖ ⟶ G'ₙ` of the `ℓ`-adic image tower are cokernels of `ℓⁿ`.** -/
noncomputable def isColimitCokernelCofork {n k : ℕ} (h : n ≤ k) :
    IsColimit (CokernelCofork.ofπ ((H.adicImageTower ℓ c).map (homOfLE h).op)
      (AdicTowerStructure.pow_smul_id_comp_map_eq_zero _ ℓ
        (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero) h)) :=
  have := hH.epi_adicImageTower_map h
  ShortComplex.Exact.gIsCokernel (S := ShortComplex.mk _ _
    (AdicTowerStructure.pow_smul_id_comp_map_eq_zero _ ℓ
      (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero) h))
    (exact_of_forall_sheafFiber fun x y hy ↦ by
      obtain ⟨w, hw⟩ := H.exists_pow_smul_eq_of_map_adicImageTower_map_eq_zero ℓ c _
        (hH.exists_eval_eq (X.algClosurePoint x)) (hH.eval_eq_zero_iff (X.algClosurePoint x))
        h y hy
      exact ⟨w, (sheafFiber_map_nsmul_id_apply _ _ _ _).trans hw⟩)

include hH in
/-- **The `ℓ`-adic image tower is flat**: `G'ₙ₊ₘ --ℓⁿ--> G'ₙ₊ₘ --ℓᵐ--> G'ₙ₊ₘ` is exact. -/
lemma exact_pow_smul_adicImageTower (n m : ℕ) :
    (ShortComplex.mk _ _ (AdicTowerStructure.pow_smul_id_comp_pow_smul_id_eq_zero _ ℓ
      (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero) n m)).Exact :=
  exact_of_forall_sheafFiber fun x y hy ↦ by
    obtain ⟨w, hw⟩ := H.exists_pow_smul_eq_of_pow_smul_eq_zero_adicImageTower ℓ c _
      (hH.exists_eval_eq (X.algClosurePoint x)) (hH.eval_eq_zero_iff (X.algClosurePoint x))
      (hH.pow_smul_eq_zero (X.algClosurePoint x)) n m y
      ((sheafFiber_map_nsmul_id_apply _ _ _ _).symm.trans hy)
    exact ⟨w, (sheafFiber_map_nsmul_id_apply _ _ _ _).trans hw⟩

/-- **The `ℓ`-adic image tower of a uniformly Artin-Rees tower is an `ℓ`-adic tower**: its
transition maps are cokernels of powers of `ℓ` and it is flat
(`CategoryTheory.AdicTowerStructure.ofIsColimit`). -/
noncomputable def adicTowerStructure : AdicTowerStructure (H.adicImageTower ℓ c) ℓ :=
  AdicTowerStructure.ofIsColimit _ ℓ (H.adicImageTower_pow_smul_id_eq_zero ℓ c hzero)
    (fun h ↦ hH.isColimitCokernelCofork hzero h) (hH.exact_pow_smul_adicImageTower hzero)

include hH in
/-- **The stalks of the `ℓ`-adic image tower are `(Λ / ℓᵐ)ʳ`.** Over a discrete valuation ring
`Λ` in which `ℓ` is a nonzero nonunit, if the limit `L_s` of the tower of stalks of `H` at a
geometric point `s` is finitely generated, then there is `r` (the rank of `ℓᶜ L_s`) such that the
stalk of `G'ₘ` at `s` is isomorphic to `(Λ / ℓᵐ)ʳ` for every `m`. -/
theorem exists_linearEquiv_sheafFiber [IsDomain Λ] [IsDiscreteValuationRing Λ]
    (hℓ : (ℓ : Λ) ≠ 0) (hℓ' : ¬IsUnit (ℓ : Λ)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X)
    [Module.Finite Λ (ModuleCat.sectionsSubmodule (H ⋙ (pointSmallEtale s).sheafFiber))] :
    ∃ r : ℕ, ∀ m : ℕ, Nonempty ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((H.adicImageTower ℓ c).obj (op m)) ≃ₗ[Λ] (Fin r → Λ ⧸ Ideal.span {(ℓ : Λ) ^ m})) :=
  H.exists_linearEquiv_map_adicImageTower ℓ c _ (hH.exists_eval_eq s) (hH.eval_eq_zero_iff s)
    hℓ hℓ' (hH.pow_smul_eq_zero s)

include hH in
/-- **The rank of the `ℓ`-adic image tower is locally constant**, hence constant on a connected
scheme: over a discrete valuation ring `Λ` in which `ℓ` is a nonzero nonunit, if the `Hₙ` are
finite locally constant and the limits of the towers of stalks are finitely generated, there is
`r` such that every stalk of every `G'ₘ` is isomorphic to `(Λ / ℓᵐ)ʳ`. -/
theorem exists_forall_linearEquiv_sheafFiber [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [ConnectedSpace X] (hℓ : (ℓ : Λ) ≠ 0) (hℓ' : ¬IsUnit (ℓ : Λ))
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (H.obj (op n))]
    (hfin : ∀ x : X, Module.Finite Λ (ModuleCat.sectionsSubmodule
      (H ⋙ (pointSmallEtale (X.algClosurePoint x)).sheafFiber))) :
    ∃ r : ℕ, ∀ (m : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
        ((H.adicImageTower ℓ c).obj (op m)) ≃ₗ[Λ] (Fin r → Λ ⧸ Ideal.span {(ℓ : Λ) ^ m})) := by
  choose r hr using fun x : X ↦
    have := hfin x
    hH.exists_linearEquiv_sheafFiber hℓ hℓ' (X.algClosurePoint x)
  have hI : Ideal.span {(ℓ : Λ) ^ 1} ≠ ⊤ := by
    rwa [pow_one, Ne, Ideal.span_singleton_eq_top]
  have : Nontrivial (Λ ⧸ Ideal.span {(ℓ : Λ) ^ 1}) := Ideal.Quotient.nontrivial_iff.2 hI
  -- the rank is determined by the stalk of `G'₁`
  have hrank {a b : ℕ} (e : (Fin a → Λ ⧸ Ideal.span {(ℓ : Λ) ^ 1}) ≃ₗ[Λ]
      (Fin b → Λ ⧸ Ideal.span {(ℓ : Λ) ^ 1})) : a = b := by
    have := (e.extendScalarsOfSurjective (S := Λ ⧸ Ideal.span {(ℓ : Λ) ^ 1})
      Ideal.Quotient.mk_surjective).finrank_eq
    rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at this
  have hloc : IsLocallyConstant r := (IsLocallyConstant.iff_exists_open r).2 fun x ↦ by
    obtain ⟨U, hU, hxU, N, hN⟩ :=
      exists_isOpen_nonempty_sheafFiber_iso ((H.adicImageTower ℓ c).obj (op 1)) x
    refine ⟨U, hU, hxU, fun y hy ↦ ?_⟩
    obtain ⟨ex⟩ := hN _ (X.algClosurePoint x) (by rwa [algClosurePoint_base])
    obtain ⟨ey⟩ := hN _ (X.algClosurePoint y) (by rwa [algClosurePoint_base])
    obtain ⟨fx⟩ := hr x 1
    obtain ⟨fy⟩ := hr y 1
    exact hrank (fy.symm ≪≫ₗ (ey ≪≫ ex.symm).toLinearEquiv ≪≫ₗ fx)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine ⟨r x₀, fun m Ω _ _ s ↦ ?_⟩
  let x := s.base (IsLocalRing.closedPoint Ω)
  obtain ⟨e⟩ := nonempty_sheafFiber_iso_of_isLocallyConstantSheaf
    ((H.adicImageTower ℓ c).obj (op m)) s (X.algClosurePoint x) (by rw [algClosurePoint_base])
  obtain ⟨f⟩ := hr x m
  rw [hloc.apply_eq_of_preconnectedSpace x x₀] at f
  exact ⟨e.toLinearEquiv ≪≫ₗ f⟩

end IsArtinReesTower

/-- **A locally constant sheaf with all stalks isomorphic to `M` is étale locally isomorphic to
the constant sheaf `M`**: on the nonempty members of a trivialising cover, the value of the
constant sheaf is a stalk. -/
theorem exists_cover_nonempty_iso_constantSheaf
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F]
    (M : ModuleCat.{u + 1} Λ)
    (hM : ∀ x : X, Nonempty ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F ≅ M)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      Nonempty (((𝒰.f i)^*[ModuleCat.{u + 1} Λ]).obj F ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  refine ⟨𝒰.nonemptyMembers, fun i ↦ ?_⟩
  have : Etale (𝒰.f i.1) := 𝒰.map_prop i.1
  obtain ⟨N, ⟨e⟩⟩ := ((isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i.1) F).1
    (hc i.1)).mem_essImage
  obtain ⟨v⟩ := i.2
  obtain ⟨eN⟩ := nonempty_sheafFiber_iso_of_iso F (𝒰.f i.1) e.symm
    (X.algClosurePoint ((𝒰.f i.1).base v)) (by rw [algClosurePoint_base]; exact ⟨v, rfl⟩)
  obtain ⟨eM⟩ := hM ((𝒰.f i.1).base v)
  exact ⟨e.symm ≪≫ (constantSheaf _ _).mapIso (eN.symm ≪≫ eM)⟩


end AlgebraicGeometry.Etale
