import Langlands.Cohomology.ModuleComplex.NatModuleQuasiIsoCriterionStatement

set_option autoImplicit false

universe u

open CategoryTheory

namespace Langlands.Cohomology.ModuleComplex

private lemma homologyπ_eq_iff_boundary
    {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
    (x y : S.cycles) :
    S.homologyπ x = S.homologyπ y ↔
      S.iCycles x - S.iCycles y ∈ LinearMap.range S.f.hom := by
  have fac (z : S.cycles) :
      S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) :=
    congrArg (fun f : S.cycles ⟶ S.opcycles => f z) S.homology_π_ι
  rw [← S.moduleCat_pOpcycles_eq_iff]
  constructor
  · intro h
    rw [← fac x, ← fac y, h]
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).1 inferInstance
    rw [fac x, fac y, h]

private lemma homologyπ_eq_zero_iff_boundary
    {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
    (x : S.cycles) :
    S.homologyπ x = 0 ↔ S.iCycles x ∈ LinearMap.range S.f.hom := by
  simpa using homologyπ_eq_iff_boundary S x 0

private lemma shortComplex_quasiIso_of_cycle_tests
    {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{u} R)}
    (φ : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 →
      φ.τ₂ x ∈ LinearMap.range T.f.hom → x ∈ LinearMap.range S.f.hom)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ φ.τ₂ x - y ∈ LinearMap.range T.f.hom) :
    ShortComplex.QuasiIso φ := by
  have cycle_natural (x : S.cycles) :
      T.iCycles (ShortComplex.cyclesMap φ x) = φ.τ₂ (S.iCycles x) :=
    congrArg (fun f : S.cycles ⟶ T.X₂ => f x) (ShortComplex.cyclesMap_i φ)
  have homology_natural (x : S.cycles) :
      ShortComplex.homologyMap φ (S.homologyπ x) =
        T.homologyπ (ShortComplex.cyclesMap φ x) :=
    congrArg (fun f : S.cycles ⟶ T.homology => f x)
      (ShortComplex.homologyπ_naturality φ)
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (injective_iff_map_eq_zero (ShortComplex.homologyMap φ).hom).2
    intro h hh
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance h
    rw [homology_natural] at hh
    have hb := (homologyπ_eq_zero_iff_boundary T _).1 hh
    rw [cycle_natural] at hb
    apply (homologyπ_eq_zero_iff_boundary S x).2
    apply hinj (S.iCycles x) _ hb
    exact congrArg (fun f : S.cycles ⟶ S.X₃ => f x) S.iCycles_g
  · intro h
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance h
    have hy : T.g (T.iCycles y) = 0 :=
      congrArg (fun f : T.cycles ⟶ T.X₃ => f y) T.iCycles_g
    obtain ⟨x, hx, hxy⟩ := hsurj (T.iCycles y) hy
    let z : S.cycles := S.cyclesMk x hx
    have hz : S.iCycles z = x := S.i_cyclesMk x hx
    refine ⟨S.homologyπ z, ?_⟩
    rw [homology_natural]
    apply (homologyπ_eq_iff_boundary T _ y).2
    simpa only [cycle_natural, hz] using hxy

/-- Explicit cycle and boundary tests imply a categorical quasi-isomorphism. -/
theorem natModuleQuasiIsoCriterion : NatModuleQuasiIsoCriterionStatement.{u} := by
  intro R _ K C φ h₀inj h₀surj hposinj hpossurj
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      apply shortComplex_quasiIso_of_cycle_tests
      · change ∀ (x : K.X 0), K.d 0 1 x = 0 →
          φ.f 0 x ∈ LinearMap.range (C.d 0 0).hom →
          x ∈ LinearMap.range (K.d 0 0).hom
        intro x hx hφx
        change φ.f 0 x ∈ LinearMap.range (C.d 0 0).hom at hφx
        have hφzero : φ.f 0 x = 0 := by simpa using hφx
        have hxzero := h₀inj x hx hφzero
        change x ∈ LinearMap.range (K.d 0 0).hom
        rw [hxzero]
        exact (LinearMap.range _).zero_mem
      · change ∀ (y : C.X 0), C.d 0 1 y = 0 →
          ∃ x : K.X 0, K.d 0 1 x = 0 ∧
            φ.f 0 x - y ∈ LinearMap.range (C.d 0 0).hom
        intro y hy
        obtain ⟨x, hx, hxy⟩ := h₀surj y hy
        refine ⟨x, hx, ?_⟩
        rw [hxy, sub_self]
        exact (LinearMap.range _).zero_mem
  | succ i =>
      rw [quasiIsoAt_iff' φ i (i + 1) (i + 2) (by simp) (by simp)]
      exact shortComplex_quasiIso_of_cycle_tests _ (hposinj i) (hpossurj i)

end Langlands.Cohomology.ModuleComplex
