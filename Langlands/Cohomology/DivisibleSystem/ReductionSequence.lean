import Langlands.Cohomology.DivisibleSystem.AdicLimit
import Langlands.Cohomology.DivisibleSystem.InverseLimit

/-!
# Reduction sequences for inverse limits of `ℓ`-divisible systems

Milne, *Étale Cohomology* (1980), Ch. V, §1, Lemma 1.11, printed p.165: "Let `F = (F_n)` be an
`l`-adic sheaf on `X_et` such that each `F_n` is flat as a sheaf of `ℤ/(l^n)`-modules and
`H^r(X, F_n)` is finite for all `r` and `n`. Then `H^r(X, F)` is finitely generated as a
`ℤ_l`-module and there are exact sequences
`0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0` for all `r` and `n`."
Here `H^r(X, F) = lim_n H^r(X, F_n)` (p.164), and `M^(n)` and `M_n` are the cokernel and the
kernel of multiplication by `n` on `M` (Notation, p.xiii). Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, §2, p.306, Lemma 2.8, identifies the cohomology of
the inverse limit `lim C_m^•` of an `ℓ`-divisible system of complexes with `lim H^q`.

This module proves Lemma 1.11 for an `ℓ`-divisible system `T` of complexes (the published
`DivisibleSystem` in `HomologicalComplex C c`) through the limit complex `L`, not through
Milne's tensor-product argument:

* `cokernelKernelShortComplex`, `cokernelKernelShortComplex_shortExact`: a sequence
  `A ⟶ B ⟶ X ⟶ D ⟶ E` exact at `B`, `X` and `D` gives a short exact sequence
  `0 ⟶ coker (A ⟶ B) ⟶ X ⟶ ker (D ⟶ E) ⟶ 0`; `homologyCokernelKernelShortComplex` and
  `homologyCokernelKernelShortComplex_shortExact` apply it to the homology sequence of a short
  exact sequence of complexes; `homologyMap_powSMul`.
* `reductionShortComplex L n`: `L ⟶ L ⟶ T n` (multiplication by `ℓ ^ n`, then the projection)
  for a cone `L` over `T.tower`. It is short exact for a limit cone when a faithful exact
  functor to modules preserves the limit (`reductionShortComplex_shortExact_of_faithful`, for
  systems in `C`; `reductionShortComplex_shortExact_of_degreewise`, for complexes), and in
  particular for complexes of modules and of representations
  (`reductionShortComplex_shortExact_moduleCat`, `reductionShortComplex_shortExact_rep`).
* `reductionSequence`, `reductionSequence_shortExact`: if `0 ⟶ L ⟶ L ⟶ T n ⟶ 0` is short
  exact, then `0 ⟶ H^i(L) / ℓ ^ n ⟶ H^i(T n) ⟶ H^j(L)[ℓ ^ n] ⟶ 0` is short exact for
  `c.Rel i j`, with first map induced by the projection (`reductionπ_reductionSequence_f`) and
  second map the connecting map (`reductionSequence_g_ι`).
* `inverseLimitReductionSequence`, `inverseLimitReductionSequence_shortExact`: Milne's form,
  with `H^r(L)` replaced by `lim_m H^r(T m)`, when the published comparisons
  `inverseLimitHomologyComparison` in degrees `i` and `j` are isomorphisms;
  `inverseLimitReductionSequence_shortExact_of_finite` and
  `inverseLimitReductionSequence_shortExact_rep`: for `ℤ`-graded complexes of modules or of
  representations with finite cohomology, given Worker 3's
  `FiniteCohomologyInverseLimitStatement` (used as a hypothesis).

Not formalized: finite generation of `H^r(X, F)` over `ℤ_l`, and étale sheaves. Milne's
flatness hypothesis is part of the published `DivisibleSystem` axioms. The statements and proofs
are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v u' v'

section FourTerm

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For maps `A ⟶ B ⟶ X ⟶ D ⟶ E` with zero consecutive composites, the short complex
`coker (A ⟶ B) ⟶ X ⟶ ker (D ⟶ E)` induced by `B ⟶ X` and `X ⟶ D`. -/
def cokernelKernelShortComplex {A B X D E : C} (f : A ⟶ B) (g : B ⟶ X) (δ : X ⟶ D) (h : D ⟶ E)
    (hfg : f ≫ g = 0) (hgδ : g ≫ δ = 0) (hδh : δ ≫ h = 0) : ShortComplex C :=
  ShortComplex.mk (cokernel.desc f g hfg) (kernel.lift h δ hδh) (by
    ext
    simp [hgδ])

/-- If `A ⟶ B ⟶ X ⟶ D ⟶ E` is exact at `B`, `X` and `D`, then
`0 ⟶ coker (A ⟶ B) ⟶ X ⟶ ker (D ⟶ E) ⟶ 0` is short exact. -/
theorem cokernelKernelShortComplex_shortExact {A B X D E : C} {f : A ⟶ B} {g : B ⟶ X}
    {δ : X ⟶ D} {h : D ⟶ E} {hfg : f ≫ g = 0} {hgδ : g ≫ δ = 0} {hδh : δ ≫ h = 0}
    (h₁ : (ShortComplex.mk f g hfg).Exact) (h₂ : (ShortComplex.mk g δ hgδ).Exact)
    (h₃ : (ShortComplex.mk δ h hδh).Exact) :
    (cokernelKernelShortComplex f g δ h hfg hgδ hδh).ShortExact := by
  let S₂ : ShortComplex C := ShortComplex.mk (cokernel.desc f g hfg) δ (by
    ext
    simp [hgδ])
  let φ₁ : ShortComplex.mk g δ hgδ ⟶ S₂ :=
    { τ₁ := cokernel.π f
      τ₂ := 𝟙 X
      τ₃ := 𝟙 D
      comm₁₂ := by simp [S₂]
      comm₂₃ := by simp [S₂] }
  let φ₂ : cokernelKernelShortComplex f g δ h hfg hgδ hδh ⟶ S₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 X
      τ₃ := kernel.ι h
      comm₁₂ := by simp [S₂, cokernelKernelShortComplex]
      comm₂₃ := by simp [S₂, cokernelKernelShortComplex] }
  have hS₂ : S₂.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₁).1 h₂
  have : Epi φ₂.τ₁ := show Epi (𝟙 _) from inferInstance
  have : IsIso φ₂.τ₂ := show IsIso (𝟙 X) from inferInstance
  have : Mono φ₂.τ₃ := show Mono (kernel.ι h) from inferInstance
  exact
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ₂).2 hS₂
      mono_f := h₁.mono_cokernelDesc
      epi_g := h₃.epi_kernelLift }

end FourTerm

section HomologySequence

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of complexes and `c.Rel i j`, the short
complex `coker (H^i X₁ ⟶ H^i X₂) ⟶ H^i X₃ ⟶ ker (H^j X₁ ⟶ H^j X₂)` given by the map induced
by `X₂ ⟶ X₃` and by the connecting map. -/
def homologyCokernelKernelShortComplex : ShortComplex C :=
  cokernelKernelShortComplex (HomologicalComplex.homologyMap S.f i)
    (HomologicalComplex.homologyMap S.g i) (hS.δ i j hij) (HomologicalComplex.homologyMap S.f j)
    (by rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])
    (hS.comp_δ i j hij) (hS.δ_comp i j hij)

/-- The short complex `homologyCokernelKernelShortComplex` is short exact. -/
theorem homologyCokernelKernelShortComplex_shortExact :
    (homologyCokernelKernelShortComplex hS i j hij).ShortExact :=
  cokernelKernelShortComplex_shortExact (hS.homology_exact₂ i) (hS.homology_exact₃ i j hij)
    (hS.homology_exact₁ i j hij)

end HomologySequence

/-- The map induced on homology by multiplication by `ℓ ^ n` is multiplication by `ℓ ^ n`. -/
lemma homologyMap_powSMul {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (ℓ n : ℕ) (K : HomologicalComplex C c) (i : ι) :
    HomologicalComplex.homologyMap (powSMul ℓ n K) i = powSMul ℓ n (K.homology i) :=
  map_powSMul (HomologicalComplex.homologyFunctor C c i) ℓ n K

namespace DivisibleSystem

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ} {T : DivisibleSystem C ℓ}
  (L : Cone T.tower) (n : ℕ)

/-- The short complex `L ⟶ L ⟶ T n` of multiplication by `ℓ ^ n` on the vertex of a cone over
`T`, followed by the projection. -/
abbrev reductionShortComplex : ShortComplex C :=
  ShortComplex.mk (powSMul ℓ n L.pt) (L.π.app (op n)) (powSMul_comp_π L n)

end Abelian

section Faithful

variable {C : Type u'} [Category.{v'} C] [Abelian C] {R : Type u} [CommRing R] {ℓ : ℕ}
  {T : DivisibleSystem C ℓ} {L : Cone T.tower} (hL : IsLimit L)
  (F : C ⥤ ModuleCat.{w} R) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Faithful] [PreservesLimitsOfShape ℕᵒᵖ F]

include hL F in
/-- If a faithful exact functor `F` to modules preserves the limit `L` of `T`, then
`0 ⟶ L ⟶ L ⟶ T n ⟶ 0`, given by `ℓ ^ n` and the projection, is short exact. -/
theorem reductionShortComplex_shortExact_of_faithful (n : ℕ) :
    (reductionShortComplex L n).ShortExact := by
  have : Mono (powSMul ℓ 1 L.pt) := mono_powSMul_one_of_faithful hL F
  exact
    { exact := ShortComplex.exact_of_g_is_cokernel _ (isCokernelOfFaithful hL F n)
      mono_f := mono_powSMul ℓ L.pt n
      epi_g := epi_of_isColimit_cofork (isCokernelOfFaithful hL F n) }

end Faithful

section Complexes

variable {C : Type u'} [Category.{v'} C] [Abelian C] {ι : Type*} {c : ComplexShape ι} {ℓ : ℕ}
  {T : DivisibleSystem (HomologicalComplex C c) ℓ} {L : Cone T.tower}

section Sequence

variable {n : ℕ} (hS : (reductionShortComplex L n).ShortExact) (i j : ι) (hij : c.Rel i j)

/-- Milne's sequence `H^i(L) / ℓ ^ n ⟶ H^i(T n) ⟶ H^j(L)[ℓ ^ n]` for a cone `L` over an
`ℓ`-divisible system of complexes with `0 ⟶ L ⟶ L ⟶ T n ⟶ 0` short exact: the first map is
induced by the projection, the second by the connecting map. -/
def reductionSequence : ShortComplex C :=
  cokernelKernelShortComplex (powSMul ℓ n (L.pt.homology i))
    (HomologicalComplex.homologyMap (L.π.app (op n)) i) (hS.δ i j hij)
    (powSMul ℓ n (L.pt.homology j))
    (by rw [← homologyMap_powSMul, ← HomologicalComplex.homologyMap_comp, powSMul_comp_π,
      HomologicalComplex.homologyMap_zero])
    (hS.comp_δ i j hij) (by rw [← homologyMap_powSMul]; exact hS.δ_comp i j hij)

/-- The projection `H^i(L) ⟶ H^i(L) / ℓ ^ n` followed by the first map of `reductionSequence`
is the map induced on homology by the projection `L ⟶ T n`. -/
@[reassoc (attr := simp)]
lemma reductionπ_reductionSequence_f :
    reductionπ ℓ (L.pt.homology i) n ≫ (reductionSequence hS i j hij).f =
      HomologicalComplex.homologyMap (L.π.app (op n)) i :=
  cokernel.π_desc _ _ _

/-- The second map of `reductionSequence` followed by the inclusion of the `ℓ ^ n`-torsion is the
connecting map. -/
@[reassoc (attr := simp)]
lemma reductionSequence_g_ι :
    (reductionSequence hS i j hij).g ≫ kernel.ι (powSMul ℓ n (L.pt.homology j)) =
      hS.δ i j hij :=
  kernel.lift_ι _ _ _

/-- Milne, Ch. V, Lemma 1.11: `0 ⟶ H^i(L) / ℓ ^ n ⟶ H^i(T n) ⟶ H^j(L)[ℓ ^ n] ⟶ 0` is short
exact. -/
theorem reductionSequence_shortExact : (reductionSequence hS i j hij).ShortExact :=
  cokernelKernelShortComplex_shortExact
    (shortComplex_exact_congr (homologyMap_powSMul ℓ n L.pt i) rfl (hS.homology_exact₂ i))
    (hS.homology_exact₃ i j hij)
    (shortComplex_exact_congr rfl (homologyMap_powSMul ℓ n L.pt j) (hS.homology_exact₁ i j hij))

end Sequence

section Degreewise

variable [HasLimitsOfShape ℕᵒᵖ C] {R : Type u} [CommRing R] (hL : IsLimit L)
  (F : C ⥤ ModuleCat.{w} R) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Faithful] [PreservesLimitsOfShape ℕᵒᵖ F]

include hL F in
/-- If a faithful exact functor `F` to modules preserves limits over `ℕᵒᵖ`, then for a limit
`L` of an `ℓ`-divisible system of complexes `0 ⟶ L ⟶ L ⟶ T n ⟶ 0` is short exact. -/
theorem reductionShortComplex_shortExact_of_degreewise (n : ℕ) :
    (reductionShortComplex L n).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun q =>
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp))
      (reductionShortComplex_shortExact_of_faithful (T := T.degree q)
        (L := (HomologicalComplex.eval C c q).mapCone L)
        (isLimitOfPreserves (HomologicalComplex.eval C c q) hL) F n)

end Degreewise

section InverseLimit

variable [HasLimitsOfShape ℕᵒᵖ C]

omit [HasLimitsOfShape ℕᵒᵖ C] in
variable (T) in
/-- Multiplication by `ℓ ^ n` on the homology of `T n` is zero. -/
lemma powSMul_homology_eq_zero (n : ℕ) (i : ι) :
    powSMul ℓ n ((T.tower ⋙ HomologicalComplex.homologyFunctor C c i).obj (op n)) = 0 := by
  change powSMul ℓ n ((HomologicalComplex.homologyFunctor C c i).obj (T.tower.obj (op n))) = 0
  rw [← map_powSMul, T.powSMul_eq_zero, Functor.map_zero]

variable {n : ℕ} (hS : (reductionShortComplex (limit.cone T.tower) n).ShortExact) (i j : ι)
  (hij : c.Rel i j)

/-- Milne's sequence with `H^r` of the limit replaced by `lim_m H^r(T m)`: the short complex
`(lim_m H^i(T m)) / ℓ ^ n ⟶ H^i(T n) ⟶ (lim_m H^j(T m))[ℓ ^ n]` whose first map is induced by the
projection and whose second map is the connecting map followed by the comparison
`inverseLimitHomologyComparison` in degree `j`. The comparison in degree `i` is assumed to be an
isomorphism, which is used to show that the composite of the two maps vanishes. -/
def inverseLimitReductionSequence (hi : IsIso (T.inverseLimitHomologyComparison i)) :
    ShortComplex C :=
  cokernelKernelShortComplex
    (powSMul ℓ n (limit (T.tower ⋙ HomologicalComplex.homologyFunctor C c i)))
    (limit.π (T.tower ⋙ HomologicalComplex.homologyFunctor C c i) (op n))
    (hS.δ i j hij ≫ T.inverseLimitHomologyComparison j)
    (powSMul ℓ n (limit (T.tower ⋙ HomologicalComplex.homologyFunctor C c j)))
    (by rw [← comp_powSMul, powSMul_homology_eq_zero, comp_zero])
    (by
      have := hi
      refine (cancel_epi (T.inverseLimitHomologyComparison i)).1 ?_
      refine ((inverseLimitHomologyComparison_π_assoc T i (op n) _).trans ?_).trans comp_zero.symm
      exact (hS.comp_δ_assoc i j hij _).trans zero_comp)
    ((Category.assoc _ _ _).trans
      ((congrArg (hS.δ i j hij ≫ ·)
        ((comp_powSMul ℓ n (T.inverseLimitHomologyComparison j)).trans
          (congrArg (· ≫ T.inverseLimitHomologyComparison j)
            (homologyMap_powSMul ℓ n T.inverseLimit j).symm))).trans
        ((hS.δ_comp_assoc i j hij _).trans zero_comp)))

variable (hi : IsIso (T.inverseLimitHomologyComparison i))

/-- The projection `lim_m H^i(T m) ⟶ (lim_m H^i(T m)) / ℓ ^ n` followed by the first map of
`inverseLimitReductionSequence` is the projection `lim_m H^i(T m) ⟶ H^i(T n)`. -/
@[reassoc (attr := simp)]
lemma reductionπ_inverseLimitReductionSequence_f :
    reductionπ ℓ (limit (T.tower ⋙ HomologicalComplex.homologyFunctor C c i)) n ≫
        (inverseLimitReductionSequence hS i j hij hi).f =
      limit.π (T.tower ⋙ HomologicalComplex.homologyFunctor C c i) (op n) :=
  cokernel.π_desc _ _ _

/-- The second map of `inverseLimitReductionSequence` followed by the inclusion of the
`ℓ ^ n`-torsion is the connecting map followed by the comparison in degree `j`. -/
@[reassoc (attr := simp)]
lemma inverseLimitReductionSequence_g_ι :
    (inverseLimitReductionSequence hS i j hij hi).g ≫
        kernel.ι (powSMul ℓ n (limit (T.tower ⋙ HomologicalComplex.homologyFunctor C c j))) =
      hS.δ i j hij ≫ T.inverseLimitHomologyComparison j :=
  kernel.lift_ι _ _ _

/-- Milne, Ch. V, Lemma 1.11, in its original form with `H^r = lim_m H^r(T m)`: if the comparison
maps `inverseLimitHomologyComparison` in degrees `i` and `j` are isomorphisms, then
`0 ⟶ (lim_m H^i(T m)) / ℓ ^ n ⟶ H^i(T n) ⟶ (lim_m H^j(T m))[ℓ ^ n] ⟶ 0` is short exact. -/
theorem inverseLimitReductionSequence_shortExact
    (hj : IsIso (T.inverseLimitHomologyComparison j)) :
    (inverseLimitReductionSequence hS i j hij hi).ShortExact := by
  refine cokernelKernelShortComplex_shortExact ?_ ?_ ?_
  · refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₂ i)
    exact ShortComplex.isoMk (asIso (T.inverseLimitHomologyComparison i))
      (asIso (T.inverseLimitHomologyComparison i)) (Iso.refl _)
      ((comp_powSMul ℓ n (T.inverseLimitHomologyComparison i)).trans
        (congrArg (· ≫ T.inverseLimitHomologyComparison i)
          (homologyMap_powSMul ℓ n T.inverseLimit i).symm))
      ((inverseLimitHomologyComparison_π T i (op n)).trans (Category.comp_id _).symm)
  · refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₃ i j hij)
    exact ShortComplex.isoMk (asIso (T.inverseLimitHomologyComparison i)) (Iso.refl _)
      (asIso (T.inverseLimitHomologyComparison j))
      ((inverseLimitHomologyComparison_π T i (op n)).trans (Category.comp_id _).symm)
      (Category.id_comp _)
  · refine ShortComplex.exact_of_iso ?_ (hS.homology_exact₁ i j hij)
    exact ShortComplex.isoMk (Iso.refl _) (asIso (T.inverseLimitHomologyComparison j))
      (asIso (T.inverseLimitHomologyComparison j)) (Category.id_comp _)
      ((comp_powSMul ℓ n (T.inverseLimitHomologyComparison j)).trans
        (congrArg (· ≫ T.inverseLimitHomologyComparison j)
          (homologyMap_powSMul ℓ n T.inverseLimit j).symm))

end InverseLimit

end Complexes

section Modules

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hF : FiniteCohomologyInverseLimitStatement.{u, v} R)
  (T : DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℤ) ℓ)
  (hfin : ∀ m q, Finite ((T.obj m).homology q))

/-- For an `ℓ`-divisible system `T` of `ℤ`-graded complexes of `R`-modules, `0 ⟶ lim T ⟶ lim T ⟶
T n ⟶ 0` (given by `ℓ ^ n` and the projection) is short exact. -/
theorem reductionShortComplex_shortExact_moduleCat (n : ℕ) :
    (reductionShortComplex (limit.cone T.tower) n).ShortExact :=
  reductionShortComplex_shortExact_of_degreewise (limit.isLimit T.tower) (𝟭 _) n

include hF hfin in
/-- Milne, Ch. V, Lemma 1.11, for complexes of modules: given
`FiniteCohomologyInverseLimitStatement`, if `T` is an `ℓ`-divisible system of `ℤ`-graded complexes
of `R`-modules with finite cohomology, then
`0 ⟶ (lim_m H^q(T m)) / ℓ ^ n ⟶ H^q(T n) ⟶ (lim_m H^(q+1)(T m))[ℓ ^ n] ⟶ 0` is short exact. -/
theorem inverseLimitReductionSequence_shortExact_of_finite (n : ℕ) (q : ℤ) :
    (inverseLimitReductionSequence (reductionShortComplex_shortExact_moduleCat T n) q (q + 1) rfl
      (isIso_inverseLimitHomologyComparison_of_finite hF T hfin q)).ShortExact :=
  inverseLimitReductionSequence_shortExact _ _ _ _ _
    (isIso_inverseLimitHomologyComparison_of_finite hF T hfin (q + 1))

end Modules

section Rep

variable {k : Type u} [CommRing k] {G : Type v} [Monoid G] {ℓ : ℕ}
  (hF : FiniteCohomologyInverseLimitStatement.{u, w} k)
  (T : DivisibleSystem (CochainComplex (Rep.{w} k G) ℤ) ℓ)
  (hfin : ∀ m q, Finite ((T.obj m).homology q))

/-- For an `ℓ`-divisible system `T` of `ℤ`-graded complexes of representations,
`0 ⟶ lim T ⟶ lim T ⟶ T n ⟶ 0` (given by `ℓ ^ n` and the projection) is short exact. -/
theorem reductionShortComplex_shortExact_rep (n : ℕ) :
    (reductionShortComplex (limit.cone T.tower) n).ShortExact :=
  reductionShortComplex_shortExact_of_degreewise (limit.isLimit T.tower)
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)) n

include hF hfin in
/-- Milne, Ch. V, Lemma 1.11, for complexes of representations: given
`FiniteCohomologyInverseLimitStatement` for the coefficient ring, if `T` is an `ℓ`-divisible system
of `ℤ`-graded complexes of representations with finite cohomology, then
`0 ⟶ (lim_m H^q(T m)) / ℓ ^ n ⟶ H^q(T n) ⟶ (lim_m H^(q+1)(T m))[ℓ ^ n] ⟶ 0` is a short exact
sequence of representations. -/
theorem inverseLimitReductionSequence_shortExact_rep (n : ℕ) (q : ℤ) :
    (inverseLimitReductionSequence (reductionShortComplex_shortExact_rep T n) q (q + 1) rfl
      (isIso_inverseLimitHomologyComparison_rep hF T hfin q)).ShortExact :=
  inverseLimitReductionSequence_shortExact _ _ _ _ _
    (isIso_inverseLimitHomologyComparison_rep hF T hfin (q + 1))

end Rep

end DivisibleSystem

end Langlands.Cohomology
