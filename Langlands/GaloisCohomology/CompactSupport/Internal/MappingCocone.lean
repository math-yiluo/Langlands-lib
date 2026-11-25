import Langlands.Cohomology.Profinite.Comparison.FilteredHomology
import Langlands.Cohomology.Profinite.InnerConjugation

/-!
# The mapping cocone of `ℕ`-indexed cochain complexes of modules (internal)

For a morphism `f : K ⟶ L` of `ℕ`-indexed cochain complexes of modules, `mappingCoconeNat f` is
the complex `K ⊕ L[-1]` with differential `(x, y) ↦ (d x, f x - d y)`, written with explicit
elements (the cup products on cones of `Internal/LeibnizPairing.lean` and
`Internal/ConeSigns.lean` are computed on them). It sits in a degreewise split short exact
sequence `L[-1] ⟶ Cocone(f) ⟶ K` whose connecting map is `Hⁿ(f)` followed by
`Hⁿ(L) ≅ H^{n+1}(L[-1])`, which gives the long exact sequence
`⋯ ⟶ Hⁿ(Cocone f) ⟶ Hⁿ(K) ⟶ Hⁿ(L) ⟶ H^{n+1}(Cocone f) ⟶ ⋯` (`homology_exact₁₂₃`). The file also
has the functoriality of the cocone in commutative squares and short exact sequences, and products
of families of complexes with the identification of their homology.

This is an internal file: Mathlib's `CochainComplex.mappingCocone` (for `ℤ`-indexed complexes in a
category with homotopy cofibers) could replace it, at the cost of rewriting the explicit cup
product formulas that use this model.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

open CategoryTheory

universe u

section Cocone

variable {k : Type u} [CommRing k]

/-- The terms of the shifted complex `L[-1]`: `0` in degree `0` and `L^{n}` in degree `n + 1`. -/
noncomputable def shiftNegOneX (L : CochainComplex (ModuleCat.{u} k) ℕ) : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k PUnit
  | n + 1 => L.X n

/-- The differential of `L[-1]`: zero out of degree `0`, and `-d_L` in higher degrees. -/
noncomputable def shiftNegOneD (L : CochainComplex (ModuleCat.{u} k) ℕ) :
    ∀ n, shiftNegOneX L n ⟶ shiftNegOneX L (n + 1)
  | 0 => 0
  | n + 1 => -L.d n (n + 1)

theorem shiftNegOneD_succ_apply (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) (y : L.X n) :
    (shiftNegOneD L (n + 1)).hom y = -(L.d n (n + 1)).hom y :=
  rfl

theorem shiftNegOneD_comp (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    shiftNegOneD L n ≫ shiftNegOneD L (n + 1) = 0 := by
  cases n with
  | zero => exact Limits.zero_comp
  | succ n =>
    exact (Preadditive.neg_comp_neg _ _).trans (L.d_comp_d _ _ _)

theorem shiftNegOneD_shiftNegOneD_apply (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ)
    (y : shiftNegOneX L n) : (shiftNegOneD L (n + 1)).hom ((shiftNegOneD L n).hom y) = 0 :=
  hom_apply_hom_apply_of_comp_eq (shiftNegOneD_comp L n) y

/-- The shift `L[-1]` of an `ℕ`-indexed cochain complex of modules (the complex with `L^{n}` in
degree `n + 1` and differential `-d_L`). -/
noncomputable def shiftNegOne (L : CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (shiftNegOneX L) (shiftNegOneD L) (shiftNegOneD_comp L)

theorem shiftNegOne_d (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (shiftNegOne L).d n (n + 1) = shiftNegOneD L n :=
  CochainComplex.of_d _ _ n

/-- The identification of `L^n` with the term of `L[-1]` in degree `n + 1`. -/
def shiftNegOneSucc (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    L.X n →ₗ[k] shiftNegOneX L (n + 1) :=
  LinearMap.id

theorem shiftNegOneSucc_apply (L : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) (y : L.X n) :
    shiftNegOneSucc L n y = y :=
  rfl

variable (K L : CochainComplex (ModuleCat.{u} k) ℕ)

/-- The terms `K^n × L[-1]^n` of the mapping cocone of `f : K ⟶ L`. -/
noncomputable abbrev mappingCoconeNatX (n : ℕ) : ModuleCat.{u} k :=
  ModuleCat.of k (K.X n × shiftNegOneX L n)

variable {K L} (f : K ⟶ L)

/-- The differential `(x, y) ↦ (d x, f x + d y)` of the mapping cocone (with `f x` placed in
`L[-1]^{n+1} = L^n`). -/
noncomputable def mappingCoconeNatD (n : ℕ) :
    mappingCoconeNatX K L n ⟶ mappingCoconeNatX K L (n + 1) :=
  ModuleCat.ofHom (((K.d n (n + 1)).hom.comp (LinearMap.fst k _ _)).prod
    ((shiftNegOneSucc L n).comp ((f.f n).hom.comp (LinearMap.fst k _ _)) +
      (shiftNegOneD L n).hom.comp (LinearMap.snd k _ _)))

theorem mappingCoconeNatD_apply (n : ℕ) (x : K.X n) (y : shiftNegOneX L n) :
    (mappingCoconeNatD f n).hom (x, y) =
      ((K.d n (n + 1)).hom x, shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom y) :=
  rfl

theorem mappingCoconeNatD_comp (n : ℕ) :
    mappingCoconeNatD f n ≫ mappingCoconeNatD f (n + 1) = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
  obtain ⟨x, y⟩ := p
  change (mappingCoconeNatD f (n + 1)).hom ((mappingCoconeNatD f n).hom (x, y)) = 0
  rw [mappingCoconeNatD_apply, mappingCoconeNatD_apply]
  refine Prod.ext (hom_apply_hom_apply_of_comp_eq (K.d_comp_d _ _ _) x) ?_
  change shiftNegOneSucc L (n + 1) ((f.f (n + 1)).hom ((K.d n (n + 1)).hom x)) +
    (shiftNegOneD L (n + 1)).hom (shiftNegOneSucc L n ((f.f n).hom x) +
      (shiftNegOneD L n).hom y) = 0
  rw [map_add, shiftNegOneD_shiftNegOneD_apply, add_zero, shiftNegOneSucc_apply,
    shiftNegOneSucc_apply, shiftNegOneD_succ_apply]
  change ((f.f (n + 1)).hom ((K.d n (n + 1)).hom x) : L.X (n + 1)) +
    -(L.d n (n + 1)).hom ((f.f n).hom x) = 0
  rw [← hom_apply_hom_apply_eq_of_comp_eq (f.comm n (n + 1)) x]
  exact add_neg_cancel _

/-- The mapping cocone `Cocone(f) = K ⊕ L[-1]` of a morphism `f : K ⟶ L` of `ℕ`-indexed cochain
complexes of modules, written with explicit elements. -/
noncomputable def mappingCoconeNat : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (mappingCoconeNatX K L) (mappingCoconeNatD f) (mappingCoconeNatD_comp f)

theorem mappingCoconeNat_d (n : ℕ) :
    (mappingCoconeNat f).d n (n + 1) = mappingCoconeNatD f n :=
  CochainComplex.of_d _ _ n

/-- The projection `Cocone(f) ⟶ K`. -/
noncomputable def mappingCoconeNat.fst : mappingCoconeNat f ⟶ K :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.fst k (K.X n) (shiftNegOneX L n)))
    fun n => by
      rw [mappingCoconeNat_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The inclusion `L[-1] ⟶ Cocone(f)`. -/
noncomputable def mappingCoconeNat.inr : shiftNegOne L ⟶ mappingCoconeNat f :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.inr k (K.X n) (shiftNegOneX L n)))
    fun n => by
      rw [mappingCoconeNat_d, shiftNegOne_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun y => Prod.ext ?_ ?_)
      · exact (K.d n (n + 1)).hom.map_zero
      · show shiftNegOneSucc L n ((f.f n).hom 0) + (shiftNegOneD L n).hom y =
          (shiftNegOneD L n).hom y
        rw [map_zero, map_zero, zero_add]

end Cocone

section Pi

variable {k : Type u} [CommRing k] {ι : Type u}

/-- The product of a family of `ℕ`-indexed cochain complexes of modules, degreewise. -/
noncomputable def piComplex (K : ι → CochainComplex (ModuleCat.{u} k) ℕ) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (∀ v, (K v).X n))
    (fun n => ModuleCat.ofHom (LinearMap.pi fun v => ((K v).d n (n + 1)).hom.comp (LinearMap.proj v)))
    fun _ => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun v =>
      hom_apply_hom_apply_of_comp_eq ((K v).d_comp_d _ _ _) (x v))

theorem piComplex_d (K : ι → CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (piComplex K).d n (n + 1) = ModuleCat.ofHom
      (LinearMap.pi fun v => ((K v).d n (n + 1)).hom.comp (LinearMap.proj v)) :=
  by
  unfold piComplex
  exact CochainComplex.of_d (V := ModuleCat.{u} k) (fun n => ModuleCat.of k (∀ v, (K v).X n))
    (fun n => ModuleCat.ofHom (LinearMap.pi fun v => ((K v).d n (n + 1)).hom.comp (LinearMap.proj v)))
    n

theorem piComplex_d_hom_apply (K : ι → CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ)
    (x : (piComplex K).X n) (v : ι) :
    ((piComplex K).d n (n + 1)).hom x v = ((K v).d n (n + 1)).hom (x v) := by
  rw [piComplex_d]
  rfl

/-- The morphism into the product complex given by a family of morphisms. -/
noncomputable def piLift {M : CochainComplex (ModuleCat.{u} k) ℕ}
    {K : ι → CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, M ⟶ K v) : M ⟶ piComplex K :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (LinearMap.pi fun v => ((g v).f n).hom))
    fun n => ModuleCat.hom_ext (LinearMap.ext fun x => funext fun v => by
      change ((piComplex K).d n (n + 1)).hom _ v = ((g v).f (n + 1)).hom ((M.d n (n + 1)).hom x)
      rw [piComplex_d_hom_apply]
      exact hom_apply_hom_apply_eq_of_comp_eq ((g v).comm n (n + 1)) x)

end Pi



section ShiftHomology

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

section Shift

variable (L : CochainComplex (ModuleCat.{u} k) ℕ)

/-- `shiftNegOneSucc` as a morphism of modules. -/
noncomputable def shiftNegOneSuccHom (n : ℕ) : L.X n ⟶ (shiftNegOne L).X (n + 1) :=
  ModuleCat.ofHom (shiftNegOneSucc L n)

instance (n : ℕ) : IsIso (shiftNegOneSuccHom L n) :=
  (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

theorem shiftNegOne_d_succ_hom_apply (n : ℕ) (y : L.X n) :
    ((shiftNegOne L).d (n + 1) (n + 1 + 1)).hom (shiftNegOneSucc L n y) =
      shiftNegOneSucc L (n + 1) (-(L.d n (n + 1)).hom y) := by
  rw [shiftNegOne_d]
  rfl

@[reassoc]
theorem shiftNegOneSuccHom_d (n : ℕ) :
    shiftNegOneSuccHom L n ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
      -(L.d n (n + 1) ≫ shiftNegOneSuccHom L (n + 1)) :=
  ModuleCat.hom_ext (LinearMap.ext fun y => shiftNegOne_d_succ_hom_apply L n y)

/-- The predecessor in `ℕ` (`0 ↦ 0`), the index `(ComplexShape.up ℕ).prev`. -/
def prevNat : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

theorem up_prev_eq_prevNat (n : ℕ) : (ComplexShape.up ℕ).prev n = prevNat n := by
  cases n with
  | zero => exact CochainComplex.prev_nat_zero
  | succ n => exact CochainComplex.prev_nat_succ n

/-- The first component of the morphism of short complexes computing the homology of `L[-1]`. -/
noncomputable def shiftNegOneτ₁ : ∀ n, L.X (prevNat n) ⟶ (shiftNegOne L).X n
  | 0 => 0
  | n + 1 => -shiftNegOneSuccHom L n

/-- The morphism from the short complex of `L` at `n` to that of `L[-1]` at `n + 1`. -/
noncomputable def shiftNegOneψ (n : ℕ) :
    L.sc' (prevNat n) n (n + 1) ⟶ (shiftNegOne L).sc' n (n + 1) (n + 1 + 1) where
  τ₁ := shiftNegOneτ₁ L n
  τ₂ := shiftNegOneSuccHom L n
  τ₃ := -shiftNegOneSuccHom L (n + 1)
  comm₁₂ := by
    cases n with
    | zero =>
      change (0 : L.X 0 ⟶ (shiftNegOne L).X 0) ≫ (shiftNegOne L).d 0 (0 + 1) =
        L.d 0 0 ≫ shiftNegOneSuccHom L 0
      rw [L.shape 0 0 (by simp), zero_comp, zero_comp]
    | succ n =>
      change (-shiftNegOneSuccHom L n) ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
        L.d n (n + 1) ≫ shiftNegOneSuccHom L (n + 1)
      rw [Preadditive.neg_comp, shiftNegOneSuccHom_d, neg_neg]
  comm₂₃ := by
    change shiftNegOneSuccHom L n ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
      L.d n (n + 1) ≫ (-shiftNegOneSuccHom L (n + 1))
    rw [shiftNegOneSuccHom_d, Preadditive.comp_neg]

theorem epi_shiftNegOneτ₁ (n : ℕ) : Epi (shiftNegOneτ₁ L n) := by
  cases n with
  | zero => exact (ModuleCat.epi_iff_surjective _).2 fun (_ : PUnit) => ⟨0, rfl⟩
  | succ n =>
    refine (ModuleCat.epi_iff_surjective _).2 fun (y : L.X n) => ⟨-y, ?_⟩
    change -(-y) = y
    exact neg_neg y

theorem mono_neg_shiftNegOneSuccHom (n : ℕ) : Mono (-shiftNegOneSuccHom L n) :=
  (ModuleCat.mono_iff_injective _).2 fun (a b : L.X n) h => by
    have h' : -a = -b := h
    exact neg_injective h'

/-- The isomorphism `Hⁿ(L) ⟶ H^{n+1}(L[-1])` (with the sign of the shift). -/
noncomputable def shiftNegOneHomologyHom (n : ℕ) :
    L.homology n ⟶ (shiftNegOne L).homology (n + 1) :=
  (L.homologyIsoSc' (prevNat n) n (n + 1) (up_prev_eq_prevNat n) (CochainComplex.next ℕ n)).hom ≫
    ShortComplex.homologyMap (shiftNegOneψ L n) ≫
    ((shiftNegOne L).homologyIsoSc' n (n + 1) (n + 1 + 1) (CochainComplex.prev_nat_succ n)
      (CochainComplex.next ℕ (n + 1))).inv

instance isIso_shiftNegOneHomologyHom (n : ℕ) : IsIso (shiftNegOneHomologyHom L n) := by
  have := ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' (shiftNegOneψ L n)
    (epi_shiftNegOneτ₁ L n) (inferInstanceAs (IsIso (shiftNegOneSuccHom L n)))
    (mono_neg_shiftNegOneSuccHom L (n + 1))
  unfold shiftNegOneHomologyHom
  infer_instance

/-- `H^{n+1}(L[-1]) ≅ Hⁿ(L)`. -/
noncomputable def shiftNegOneHomologyIso (n : ℕ) :
    (shiftNegOne L).homology (n + 1) ≅ L.homology n :=
  (asIso (shiftNegOneHomologyHom L n)).symm

@[simp]
theorem shiftNegOneHomologyIso_inv (n : ℕ) :
    (shiftNegOneHomologyIso L n).inv = shiftNegOneHomologyHom L n :=
  rfl

@[simp]
theorem shiftNegOneHomologyIso_symm_hom (n : ℕ) :
    (shiftNegOneHomologyIso L n).symm.hom = shiftNegOneHomologyHom L n :=
  rfl

theorem iCycles_shiftNegOneSuccHom_d (n : ℕ) :
    (L.iCycles n ≫ shiftNegOneSuccHom L n) ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) = 0 := by
  rw [Category.assoc, shiftNegOneSuccHom_d, Preadditive.comp_neg, L.iCycles_d_assoc, zero_comp,
    neg_zero]

@[reassoc]
theorem homologyπ_shiftNegOneHomologyHom (n : ℕ) :
    L.homologyπ n ≫ shiftNegOneHomologyHom L n =
      (shiftNegOne L).liftCycles (L.iCycles n ≫ shiftNegOneSuccHom L n) (n + 1 + 1)
        (CochainComplex.next ℕ (n + 1)) (iCycles_shiftNegOneSuccHom_d L n) ≫
        (shiftNegOne L).homologyπ (n + 1) := by
  rw [shiftNegOneHomologyHom, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyπ_naturality_assoc, HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L).iCycles (n + 1))]
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    HomologicalComplex.liftCycles_i]
  rw [← HomologicalComplex.cyclesIsoSc'_hom_iCycles L (prevNat n) n (n + 1) (up_prev_eq_prevNat n)
    (CochainComplex.next ℕ n)]
  exact (congrArg (_ ≫ ·) (ShortComplex.cyclesMap_i (shiftNegOneψ L n))).trans
    (Category.assoc _ _ _).symm

end Shift

namespace mappingCoconeNat

variable {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)

@[reassoc (attr := simp)]
theorem inr_fst : inr f ≫ fst f = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The degreewise split short exact sequence `L[-1] ⟶ Cocone(f) ⟶ K`. -/
noncomputable abbrev shortComplex : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (inr f) (fst f) (inr_fst f)

theorem shortExact : (shortComplex f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro (p : K.X n × shiftNegOneX L n) hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
    mono_f := (ModuleCat.mono_iff_injective _).2 fun _ _ h => congrArg Prod.snd h
    epi_g := (ModuleCat.epi_iff_surjective _).2 fun (x : K.X n) => ⟨((x, 0) : K.X n × _), rfl⟩ }

/-- The inclusion of `Kⁿ` into the mapping cocone in degree `n` (not a map of complexes). -/
noncomputable def inlX (n : ℕ) : K.X n ⟶ (mappingCoconeNat f).X n :=
  ModuleCat.ofHom (LinearMap.inl k (K.X n) (shiftNegOneX L n))

@[reassoc (attr := simp)]
theorem inlX_fst (n : ℕ) : inlX f n ≫ (fst f).f n = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem inlX_d (n : ℕ) :
    inlX f n ≫ (mappingCoconeNat f).d n (n + 1) =
      K.d n (n + 1) ≫ inlX f (n + 1) + f.f n ≫ shiftNegOneSuccHom L n ≫ (inr f).f (n + 1) := by
  rw [mappingCoconeNat_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ ?_)
  · change (K.d n (n + 1)).hom x = (K.d n (n + 1)).hom x + 0
    rw [add_zero]
  · change shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom 0 =
      0 + shiftNegOneSucc L n ((f.f n).hom x)
    rw [map_zero, add_zero, zero_add]

theorem δ_eq (n : ℕ) :
    (shortExact f).δ n (n + 1) rfl =
      HomologicalComplex.homologyMap f n ≫ shiftNegOneHomologyHom L n := by
  refine (cancel_epi (K.homologyπ n)).1 ?_
  have h := (shortExact f).δ_eq n (n + 1) rfl (K.iCycles n) (K.iCycles_d n (n + 1))
    (K.iCycles n ≫ inlX f n) (by
      change (K.iCycles n ≫ inlX f n) ≫ (fst f).f n = K.iCycles n
      rw [Category.assoc, inlX_fst, Category.comp_id])
    (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) (by
      change (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) ≫ (inr f).f (n + 1) =
        (K.iCycles n ≫ inlX f n) ≫ (mappingCoconeNat f).d n (n + 1)
      simp only [Category.assoc]
      rw [inlX_d, Preadditive.comp_add, K.iCycles_d_assoc, zero_comp, zero_add])
    (n + 1 + 1) (CochainComplex.next ℕ (n + 1))
  have hl : K.liftCycles (K.iCycles n) (n + 1) (CochainComplex.next ℕ n) (K.iCycles_d n (n + 1)) =
      𝟙 _ := by
    rw [← cancel_mono (K.iCycles n), HomologicalComplex.liftCycles_i, Category.id_comp]
  have h2 : K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl =
      (shiftNegOne L).liftCycles (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) (n + 1 + 1)
        (CochainComplex.next ℕ (n + 1)) (by
          rw [← HomologicalComplex.cyclesMap_i_assoc, Category.assoc,
            iCycles_shiftNegOneSuccHom_d, comp_zero]) ≫
        (shiftNegOne L).homologyπ (n + 1) := by
    calc K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl =
        K.liftCycles (K.iCycles n) (n + 1) (CochainComplex.next ℕ n) (K.iCycles_d n (n + 1)) ≫
          K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl := by rw [hl, Category.id_comp]
      _ = _ := h
  rw [h2, HomologicalComplex.homologyπ_naturality_assoc, homologyπ_shiftNegOneHomologyHom]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L).iCycles (n + 1))]
  simp only [Category.assoc, HomologicalComplex.liftCycles_i, HomologicalComplex.cyclesMap_i_assoc]

/-- The connecting map `Hⁿ(L) ⟶ H^{n+1}(Cocone(f))` of the long exact sequence of the mapping
cocone. -/
noncomputable def homologyδ (n : ℕ) : L.homology n ⟶ (mappingCoconeNat f).homology (n + 1) :=
  shiftNegOneHomologyHom L n ≫ HomologicalComplex.homologyMap (inr f) (n + 1)

@[reassoc (attr := simp)]
theorem homologyMap_homologyδ (n : ℕ) :
    HomologicalComplex.homologyMap f n ≫ homologyδ f n = 0 := by
  rw [homologyδ, ← Category.assoc, ← δ_eq]
  exact (shortExact f).δ_comp n (n + 1) rfl

@[reassoc (attr := simp)]
theorem homologyδ_homologyMap_fst (n : ℕ) :
    homologyδ f n ≫ HomologicalComplex.homologyMap (fst f) (n + 1) = 0 := by
  rw [homologyδ, Category.assoc, ← HomologicalComplex.homologyMap_comp, inr_fst,
    HomologicalComplex.homologyMap_zero, comp_zero]

@[reassoc (attr := simp)]
theorem homologyMap_fst_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (fst f) n ≫ HomologicalComplex.homologyMap f n = 0 := by
  rw [← cancel_mono (shiftNegOneHomologyHom L n), Category.assoc, ← δ_eq, zero_comp]
  exact (shortExact f).comp_δ n (n + 1) rfl

theorem homology_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_homologyδ f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₁ n (n + 1) rfl)
  exact ShortComplex.isoMk (Iso.refl _) (shiftNegOneHomologyIso L n).symm (Iso.refl _)
    (by simp [δ_eq]) (by simp [homologyδ])

theorem homology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyδ_homologyMap_fst f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₂ (n + 1))
  exact ShortComplex.isoMk (shiftNegOneHomologyIso L n).symm (Iso.refl _) (Iso.refl _)
    (by simp [homologyδ]) (by simp)

theorem homology_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_fst_homologyMap f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₃ n (n + 1) rfl)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (shiftNegOneHomologyIso L n).symm
    (by simp) (by simp [δ_eq])

theorem mono_homologyMap_fst_zero : Mono (HomologicalComplex.homologyMap (fst f) 0) := by
  have hz : IsZero ((shiftNegOne L).homology 0) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of k PUnit))
  exact ((shortExact f).homology_exact₂ 0).mono_g (hz.eq_of_src _ _)

end mappingCoconeNat

end ShiftHomology

section ConeMap

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

section Shift

variable {L L' L'' : CochainComplex (ModuleCat.{u} k) ℕ}

/-- The components of the shift of a morphism of complexes. -/
noncomputable def shiftNegOneMapF (β : L ⟶ L') : ∀ n, shiftNegOneX L n ⟶ shiftNegOneX L' n
  | 0 => 0
  | n + 1 => β.f n

theorem shiftNegOneMapF_succ_apply (β : L ⟶ L') (n : ℕ) (y : L.X n) :
    (shiftNegOneMapF β (n + 1)).hom (shiftNegOneSucc L n y) = shiftNegOneSucc L' n ((β.f n).hom y) :=
  rfl

theorem shiftNegOneMapF_comm (β : L ⟶ L') (n : ℕ) :
    shiftNegOneMapF β n ≫ shiftNegOneD L' n = shiftNegOneD L n ≫ shiftNegOneMapF β (n + 1) := by
  cases n with
  | zero =>
    change shiftNegOneMapF β 0 ≫ 0 = 0 ≫ shiftNegOneMapF β 1
    rw [comp_zero, zero_comp]
  | succ n =>
    refine ModuleCat.hom_ext (LinearMap.ext fun (y : L.X n) => ?_)
    change -(L'.d n (n + 1)).hom ((β.f n).hom y) = (β.f (n + 1)).hom (-(L.d n (n + 1)).hom y)
    rw [map_neg, hom_apply_hom_apply_eq_of_comp_eq (β.comm n (n + 1)) y]

/-- The shift `β[-1] : L[-1] ⟶ L'[-1]` of a morphism of complexes. -/
noncomputable def shiftNegOneMap (β : L ⟶ L') : shiftNegOne L ⟶ shiftNegOne L' :=
  CochainComplex.ofHom (shiftNegOneMapF β) fun n =>
    ((congrArg (shiftNegOneMapF β n ≫ ·) (shiftNegOne_d L' n)).trans
      (shiftNegOneMapF_comm β n)).trans
      (congrArg (· ≫ shiftNegOneMapF β (n + 1)) (shiftNegOne_d L n)).symm

@[reassoc]
theorem shiftNegOneSuccHom_shiftNegOneMap_f (β : L ⟶ L') (n : ℕ) :
    shiftNegOneSuccHom L n ≫ (shiftNegOneMap β).f (n + 1) = β.f n ≫ shiftNegOneSuccHom L' n :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[simp]
theorem shiftNegOneMap_id : shiftNegOneMap (𝟙 L) = 𝟙 (shiftNegOne L) := by
  ext n : 1
  cases n with
  | zero => exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  | succ n => rfl

@[reassoc]
theorem shiftNegOneHomologyHom_naturality (β : L ⟶ L') (n : ℕ) :
    shiftNegOneHomologyHom L n ≫ HomologicalComplex.homologyMap (shiftNegOneMap β) (n + 1) =
      HomologicalComplex.homologyMap β n ≫ shiftNegOneHomologyHom L' n := by
  refine (cancel_epi (L.homologyπ n)).1 ?_
  rw [homologyπ_shiftNegOneHomologyHom_assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_naturality, homologyπ_shiftNegOneHomologyHom,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, HomologicalComplex.comp_liftCycles_assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L').iCycles (n + 1))]
  simp only [HomologicalComplex.liftCycles_i, Category.assoc, HomologicalComplex.cyclesMap_i_assoc,
    shiftNegOneSuccHom_shiftNegOneMap_f]

end Shift

namespace mappingCoconeNat

variable {K L K' L' K'' L'' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  {f'' : K'' ⟶ L''}

/-- The components of the morphism of mapping cocones induced by a commutative square. -/
noncomputable def mapF (α : K ⟶ K') (β : L ⟶ L') (n : ℕ) :
    (mappingCoconeNat f).X n ⟶ (mappingCoconeNat f').X n :=
  ModuleCat.ofHom ((α.f n).hom.prodMap (shiftNegOneMapF β n).hom)

theorem mapF_comm (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') (n : ℕ) :
    mapF α β n ≫ (mappingCoconeNat f').d n (n + 1) =
      (mappingCoconeNat f).d n (n + 1) ≫ mapF α β (n + 1) := by
  have wn : f.f n ≫ β.f n = α.f n ≫ f'.f n := by
    rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f]
  have hβ : ∀ y : shiftNegOneX L n, (shiftNegOneMapF β (n + 1)).hom ((shiftNegOneD L n).hom y) =
      (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom y) := fun y =>
    (hom_apply_hom_apply_eq_of_comp_eq (shiftNegOneMapF_comm β n) y).symm
  rw [mappingCoconeNat_d, mappingCoconeNat_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (α.comm n (n + 1)) p.1
  · change shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom p.1)) +
        (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom p.2) =
      (shiftNegOneMapF β (n + 1)).hom (shiftNegOneSucc L n ((f.f n).hom p.1) +
        (shiftNegOneD L n).hom p.2)
    rw [map_add, shiftNegOneMapF_succ_apply, hβ, hom_apply_hom_apply_eq_of_comp_eq wn p.1]

/-- The morphism of mapping cocones induced by a commutative square `f ≫ β = α ≫ f'`. -/
noncomputable def map (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') :
    mappingCoconeNat f ⟶ mappingCoconeNat f' :=
  CochainComplex.ofHom (mapF α β) (mapF_comm α β w)

@[simp]
theorem map_id : map (𝟙 K) (𝟙 L) (by simp) = 𝟙 (mappingCoconeNat f) := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

theorem map_comp (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') (α' : K' ⟶ K'')
    (β' : L' ⟶ L'') (w' : f' ≫ β' = α' ≫ f'') :
    map (α ≫ α') (β ≫ β') (by rw [reassoc_of% w, w', Category.assoc]) =
      map α β w ≫ map α' β' w' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

@[reassoc (attr := simp)]
theorem map_fst (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') :
    map α β w ≫ fst f' = fst f ≫ α :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
theorem inr_map (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') :
    inr f ≫ map α β w = shiftNegOneMap β ≫ inr f' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun y => Prod.ext ?_ rfl)
  exact (α.f n).hom.map_zero

@[reassoc]
theorem homologyδ_naturality (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') (n : ℕ) :
    homologyδ f n ≫ HomologicalComplex.homologyMap (map α β w) (n + 1) =
      HomologicalComplex.homologyMap β n ≫ homologyδ f' n := by
  rw [homologyδ, homologyδ, Category.assoc, ← HomologicalComplex.homologyMap_comp, inr_map,
    HomologicalComplex.homologyMap_comp, shiftNegOneHomologyHom_naturality_assoc]

section ShortExact

variable {S T : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}

/-- The short complex of mapping cocones induced by a morphism of short complexes of morphisms. -/
noncomputable def mapShortComplex (F : S ⟶ T) : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (map (f := F.τ₁) (f' := F.τ₂) S.f T.f F.comm₁₂)
    (map (f := F.τ₂) (f' := F.τ₃) S.g T.g F.comm₂₃) (by
    rw [← map_comp]
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : S.X₁.X n × shiftNegOneX T.X₁ n) =>
      Prod.ext ?_ ?_)
    · exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) S.zero) p.1
    · cases n with
      | zero => rfl
      | succ n => exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) T.zero) p.2)

theorem shortExact_mapShortComplex (F : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) :
    (mapShortComplex F).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
    have hTn := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT
    have iS := (ModuleCat.mono_iff_injective _).1 hSn.mono_f
    have sS := (ModuleCat.epi_iff_surjective _).1 hSn.epi_g
    have eS := hSn.exact
    rw [ShortComplex.moduleCat_exact_iff] at eS
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro (p : S.X₂.X n × shiftNegOneX T.X₂ n) hp
      obtain ⟨x, hx⟩ := eS p.1 (congrArg Prod.fst hp)
      cases n with
      | zero => exact ⟨(x, PUnit.unit), Prod.ext hx rfl⟩
      | succ n =>
        have eT := (hTn n).exact
        rw [ShortComplex.moduleCat_exact_iff] at eT
        obtain ⟨y, hy⟩ := eT p.2 (congrArg Prod.snd hp)
        exact ⟨(x, y), Prod.ext hx hy⟩
    · refine (ModuleCat.mono_iff_injective _).2
        fun (p q : S.X₁.X n × shiftNegOneX T.X₁ n) h => Prod.ext (iS (congrArg Prod.fst h)) ?_
      cases n with
      | zero => rfl
      | succ n => exact (ModuleCat.mono_iff_injective _).1 (hTn n).mono_f (congrArg Prod.snd h)
    · refine (ModuleCat.epi_iff_surjective _).2 fun (p : S.X₃.X n × shiftNegOneX T.X₃ n) => ?_
      obtain ⟨x, hx⟩ := sS p.1
      cases n with
      | zero => exact ⟨(x, PUnit.unit), Prod.ext hx rfl⟩
      | succ n =>
        obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 (hTn n).epi_g p.2
        exact ⟨(x, y), Prod.ext hx hy⟩

end ShortExact

end mappingCoconeNat

end ConeMap

section PiHomology

open CategoryTheory Limits


variable {k : Type u} [CommRing k]

section Pi

variable {ι : Type u} (K : ι → CochainComplex (ModuleCat.{u} k) ℕ)

theorem piComplex_d_hom_apply' (i j : ℕ) (x : (piComplex K).X i) (v : ι) :
    ((piComplex K).d i j).hom x v = ((K v).d i j).hom (x v) := by
  by_cases h : i + 1 = j
  · subst h
    exact piComplex_d_hom_apply K i x v
  · rw [(piComplex K).shape i j h, (K v).shape i j h]
    rfl

/-- The projection from the product complex to one factor. -/
noncomputable def piProj (v : ι) : piComplex K ⟶ K v :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.proj v)) fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun x => (piComplex_d_hom_apply K n x v).symm)

theorem piProj_f_hom_apply (v : ι) (n : ℕ) (x : (piComplex K).X n) :
    ((piProj K v).f n).hom x = x v :=
  rfl

@[reassoc (attr := simp)]
theorem piLift_piProj {M : CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, M ⟶ K v) (v : ι) :
    piLift g ≫ piProj K v = g v :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The comparison map from the homology of the product complex to the product of the homologies. -/
noncomputable def piHomologyToPi (n : ℕ) :
    (piComplex K).homology n ⟶ ModuleCat.of k (∀ v, (K v).homology n) :=
  ModuleCat.ofHom (LinearMap.pi fun v => (HomologicalComplex.homologyMap (piProj K v) n).hom)

theorem piHomologyToPi_hom_apply (n : ℕ) (h : (piComplex K).homology n) (v : ι) :
    (piHomologyToPi K n).hom h v = (HomologicalComplex.homologyMap (piProj K v) n).hom h :=
  rfl

theorem piHomologyToPi_bijective (n : ℕ) : Function.Bijective (piHomologyToPi K n).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective ((piComplex K).homologyπ n)).1 inferInstance h
    have hv : ∀ v, ∃ y : (K v).X ((ComplexShape.up ℕ).prev n),
        ((K v).d _ n).hom y =
          ((K v).iCycles n).hom ((HomologicalComplex.cyclesMap (piProj K v) n).hom c) := by
      intro v
      refine (homologyπ_eq_zero_iff _ _).1 ?_
      rw [← homologyMap_homologyπ_apply]
      exact congrFun hh v
    choose y hy using hv
    refine (homologyπ_eq_zero_iff _ c).2 ⟨show (piComplex K).X _ from y, funext fun v => ?_⟩
    rw [piComplex_d_hom_apply', hy v, iCycles_cyclesMap_apply]
    rfl
  · intro h
    have hv : ∀ v, ∃ c : (K v).cycles n, ((K v).homologyπ n).hom c = h v :=
      fun v => (ModuleCat.epi_iff_surjective ((K v).homologyπ n)).1 inferInstance (h v)
    choose c hc using hv
    obtain ⟨c', hc'⟩ := exists_iCycles_eq (K := piComplex K)
      (show (piComplex K).X n from fun v => ((K v).iCycles n).hom (c v)) (by
        rw [CochainComplex.next]
        funext v
        rw [piComplex_d_hom_apply]
        exact iCycles_d_apply _ n (n + 1) (c v))
    refine ⟨((piComplex K).homologyπ n).hom c', funext fun v => ?_⟩
    rw [piHomologyToPi_hom_apply, homologyMap_homologyπ_apply, ← hc v]
    congr 1
    apply (ModuleCat.mono_iff_injective ((K v).iCycles n)).1 inferInstance
    rw [iCycles_cyclesMap_apply, hc']
    rfl

/-- The homology of a product of complexes is the product of the homologies. -/
noncomputable def piHomologyIso (n : ℕ) :
    (piComplex K).homology n ≅ ModuleCat.of k (∀ v, (K v).homology n) :=
  (LinearEquiv.ofBijective (piHomologyToPi K n).hom (piHomologyToPi_bijective K n)).toModuleIso

theorem piHomologyIso_hom_apply (n : ℕ) (h : (piComplex K).homology n) (v : ι) :
    (piHomologyIso K n).hom.hom h v = (HomologicalComplex.homologyMap (piProj K v) n).hom h :=
  rfl

theorem homologyMap_piLift_piHomologyIso_hom {M : CochainComplex (ModuleCat.{u} k) ℕ}
    (g : ∀ v, M ⟶ K v) (n : ℕ) :
    HomologicalComplex.homologyMap (piLift g) n ≫ (piHomologyIso K n).hom =
      ModuleCat.ofHom (LinearMap.pi fun v => (HomologicalComplex.homologyMap (g v) n).hom) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun h => funext fun v => ?_)
  change (HomologicalComplex.homologyMap (piProj K v) n).hom
    ((HomologicalComplex.homologyMap (piLift g) n).hom h) = _
  rw [hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm h,
    piLift_piProj]
  rfl

end Pi

end PiHomology

section PiMap

variable {k : Type u} [CommRing k] {ι : Type u}

/-- The product of a family of morphisms of complexes. -/
noncomputable def piMap {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, K v ⟶ K' v) :
    piComplex K ⟶ piComplex K' :=
  piLift fun v => piProj K v ≫ g v

@[reassoc (attr := simp)]
theorem piLift_piMap {M : CochainComplex (ModuleCat.{u} k) ℕ}
    {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ} (h : ∀ v, M ⟶ K v) (g : ∀ v, K v ⟶ K' v) :
    piLift h ≫ piMap g = piLift fun v => h v ≫ g v :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
theorem piMap_piProj {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ} (g : ∀ v, K v ⟶ K' v)
    (v : ι) : piMap g ≫ piProj K' v = piProj K v ≫ g v :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem homologyMap_piMap_piHomologyIso_hom {K K' : ι → CochainComplex (ModuleCat.{u} k) ℕ}
    (g : ∀ v, K v ⟶ K' v) (n : ℕ) :
    HomologicalComplex.homologyMap (piMap g) n ≫ (piHomologyIso K' n).hom =
      (piHomologyIso K n).hom ≫ ModuleCat.ofHom (LinearMap.pi fun v =>
        (HomologicalComplex.homologyMap (g v) n).hom.comp (LinearMap.proj v)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun h => funext fun v => ?_)
  change (HomologicalComplex.homologyMap (piProj K' v) n).hom
      ((HomologicalComplex.homologyMap (piMap g) n).hom h) =
    (HomologicalComplex.homologyMap (g v) n).hom
      ((HomologicalComplex.homologyMap (piProj K v) n).hom h)
  rw [hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm h,
    hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm h, piMap_piProj]

/-- The product of a family of short complexes of complexes. -/
noncomputable def piShortComplex (S : ι → ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (piMap fun v => (S v).f) (piMap fun v => (S v).g)
    (HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
      funext fun v => hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) (S v).zero) (x v)))

theorem piShortComplex_shortExact {S : ι → ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}
    (hS : ∀ v, (S v).ShortExact) : (piShortComplex S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have h := fun v => (HomologicalComplex.shortExact_iff_degreewise_shortExact (S v)).1 (hS v) n
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro (x : ∀ v, (S v).X₂.X n) hx
      have e : ∀ v, ∃ y : (S v).X₁.X n, ((S v).f.f n).hom y = x v := fun v => by
        have ev := (h v).exact
        rw [ShortComplex.moduleCat_exact_iff] at ev
        exact ev (x v) (congrFun hx v)
      choose y hy using e
      exact ⟨show ∀ v, (S v).X₁.X n from y, funext hy⟩
    · exact (ModuleCat.mono_iff_injective _).2 fun (x x' : ∀ v, (S v).X₁.X n) hxx =>
        funext fun v => (ModuleCat.mono_iff_injective _).1 (h v).mono_f (congrFun hxx v)
    · refine (ModuleCat.epi_iff_surjective _).2 fun (z : ∀ v, (S v).X₃.X n) => ?_
      have e : ∀ v, ∃ y : (S v).X₂.X n, ((S v).g.f n).hom y = z v := fun v =>
        (ModuleCat.epi_iff_surjective _).1 (h v).epi_g (z v)
      choose y hy using e
      exact ⟨show ∀ v, (S v).X₂.X n from y, funext hy⟩

end PiMap

end Langlands.GaloisCohomology
