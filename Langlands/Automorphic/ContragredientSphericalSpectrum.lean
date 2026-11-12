import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.LocalSphericalHecke
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Automorphic.OperatorLocalRestriction
import Langlands.Representation.Unramified.PairedHeckeScalars

/-! # Spherical Hecke spectra of contragredient cuspidal realizations -/

noncomputable section
universe uF uV uW

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F]

local instance contraSpectrumRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance contraSpectrumContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance contraSpectrumSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance contraSpectrumFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance contraSpectrumStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance contraSpectrumRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance contraSpectrumLocalAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

section Generators

variable {n : ℕ} (S : OperatorRealization F n)

/-- A subspace stable under the finite translations, the compact translations and the
enveloping algebra is stable under the whole concrete operator algebra. -/
def generatorSubrepresentation (N : Submodule ℂ S.Space)
    (hd : ∀ (d : FiniteAdelicGL F n) (f : S.Space), f ∈ N → S.finiteRepresentation d f ∈ N)
    (hk : ∀ (k : standardInfiniteCompact F n) (f : S.Space), f ∈ N →
      S.compactRepresentation k f ∈ N)
    (hu : ∀ (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space), f ∈ N →
      S.envelopingAction a f ∈ N) :
    Subrepresentation S.representation where
  toSubmodule := N
  apply_mem_toSubmodule a f hf := by
    refine Algebra.adjoin_induction
      (p := fun a ha => ∀ f ∈ N, S.representation ⟨a, ha⟩ f ∈ N)
      ?_ ?_ ?_ ?_ a.property f hf
    · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩) f hf
      · exact hd d f hf
      · exact hk k f hf
      · exact hu u f hf
    · intro c f hf
      change c • f ∈ N
      exact N.smul_mem c hf
    · intro a b ha hb hLa hLb f hf
      have key : S.representation ⟨a, ha⟩ f + S.representation ⟨b, hb⟩ f ∈ N :=
        N.add_mem (hLa f hf) (hLb f hf)
      exact key
    · intro a b ha hb hLa hLb f hf
      have key : S.representation ⟨a, ha⟩ (S.representation ⟨b, hb⟩ f) ∈ N :=
        hLa _ (hLb f hf)
      exact key

/-- In an irreducible realization, a nonzero subspace stable under the three generating
families is the whole space. -/
theorem eq_top_of_generatorStable (hS : S.IsIrreducible) (N : Submodule ℂ S.Space)
    (hd : ∀ (d : FiniteAdelicGL F n) (f : S.Space), f ∈ N → S.finiteRepresentation d f ∈ N)
    (hk : ∀ (k : standardInfiniteCompact F n) (f : S.Space), f ∈ N →
      S.compactRepresentation k f ∈ N)
    (hu : ∀ (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space), f ∈ N →
      S.envelopingAction a f ∈ N)
    (hN : N ≠ ⊥) : N = ⊤ := by
  rcases hS.eq_bot_or_eq_top (S.generatorSubrepresentation N hd hk hu) with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) hN
  · exact congrArg Subrepresentation.toSubmodule h

end Generators

section Local

variable (v : FinitePlace F)

local instance contraSpectrumTopology (m : ℕ) : TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance contraSpectrumTopologicalGroup (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance contraSpectrumT2 (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance contraSpectrumMeasurable (m : ℕ) : MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance contraSpectrumBorel (m : ℕ) : BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

variable {n : ℕ} (S : OperatorRealization F n)

/-- The form inclusion intertwines the local restriction with local right translation of
forms. -/
def localFormInclusion :
    (S.localRepresentation v).IntertwiningMap (automorphicLocalRightAction F n v) where
  toLinearMap := S.formInclusion.toLinearMap
  isIntertwining' g := S.formInclusion.isIntertwining' (localInclusion F n v g)

theorem localRepresentation_apply (g : FiniteLocalGL F n v) (f : S.Space) :
    S.localRepresentation v g f = S.finiteRepresentation (localInclusion F n v g) f := rfl

theorem finiteRepresentation_mul_apply (d d' : FiniteAdelicGL F n) (f : S.Space) :
    S.finiteRepresentation d (S.finiteRepresentation d' f) = S.finiteRepresentation (d * d') f :=
  (LinearMap.congr_fun (map_mul S.finiteRepresentation d d') f).symm

@[simp] theorem localFormInclusion_apply (f : S.Space) :
    S.localFormInclusion v f = S.formInclusion f := rfl

/-- The local restriction is smooth for the canonical p-adic topology. -/
theorem localRepresentation_isSmooth_canonical :
    Langlands.IsSmooth (S.localRepresentation v) :=
  Langlands.isSmooth_of_injective (S.localFormInclusion v) S.formInclusion_injective
    (automorphicLocalRightAction_isSmooth_canonical F v n)

/-- A finite adelic element divided by its component at `v` commutes with the local
group at `v`. -/
theorem commute_localInclusion_away (d : FiniteAdelicGL F n) (g : FiniteLocalGL F n v) :
    d * (localInclusion F n v (localProjection F n v d))⁻¹ * localInclusion F n v g =
      localInclusion F n v g * (d * (localInclusion F n v (localProjection F n v d))⁻¹) := by
  apply ext_localProjection
  intro w
  by_cases h : w = v
  · subst h
    simp only [map_mul, map_inv, localProjection_localInclusion, mul_inv_cancel, one_mul,
      mul_one]
  · simp only [map_mul, map_inv, localProjection_localInclusion_of_ne _ _ _ _ h, inv_one,
      mul_one, one_mul]

end Local

section Defect

variable (v : FinitePlace F)

local instance contraDefectTopology (m : ℕ) : TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance contraDefectTopologicalGroup (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance contraDefectT2 (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance contraDefectMeasurable (m : ℕ) : MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance contraDefectBorel (m : ℕ) : BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

variable {r : ℕ} (S : OperatorRealization F (r + 1)) (s : Eigenvalues (r + 1))

/-- The defect of the spherical projection of a vector from the `i`-th standard Hecke
scalar of `s`, for the local restriction at `v`. -/
def standardDefect (i : Fin (r + 2)) : Module.End ℂ S.Space :=
  PairedHecke.heckeDefect (CompletionPadic.padicField v) (S.localRepresentation v)
    (S.localRepresentation_isSmooth_canonical v)
    (standardHeckeElement (CompletionPadic.padicField v) r i)
    (standardHeckeScalar (CompletionPadic.padicField v) s i)

/-- Operators commuting with the local action commute with the defects. -/
theorem standardDefect_commute (A : Module.End ℂ S.Space)
    (hA : ∀ g f, A (S.localRepresentation v g f) = S.localRepresentation v g (A f))
    (i : Fin (r + 2)) (f : S.Space) :
    S.standardDefect v s i (A f) = A (S.standardDefect v s i f) :=
  (PairedHecke.heckeDefect_intertwiner _ _ _ _ _
    (A.intertwiningMap_of_isIntertwiningMap _ _ hA) _ _ f).symm

/-- The vectors all of whose local translates have vanishing standard defects. -/
def defectCore : Submodule ℂ S.Space where
  carrier := {f | ∀ (g : FiniteLocalGL F (r + 1) v) (i : Fin (r + 2)),
    S.standardDefect v s i (S.localRepresentation v g f) = 0}
  zero_mem' := by
    intro g i
    simp only [map_zero]
  add_mem' := by
    intro f f' hf hf' g i
    simp only [map_add, hf g i, hf' g i, add_zero]
  smul_mem' := by
    intro c f hf g i
    simp only [map_smul, hf g i, smul_zero]

theorem mem_defectCore_iff (f : S.Space) :
    f ∈ S.defectCore v s ↔ ∀ (g : FiniteLocalGL F (r + 1) v) (i : Fin (r + 2)),
      S.standardDefect v s i (S.localRepresentation v g f) = 0 := Iff.rfl

theorem localRepresentation_mul_apply (g h : FiniteLocalGL F (r + 1) v) (f : S.Space) :
    S.localRepresentation v g (S.localRepresentation v h f) =
      S.localRepresentation v (g * h) f :=
  (LinearMap.congr_fun (map_mul (S.localRepresentation v) g h) f).symm

theorem localRepresentation_mem_defectCore (h : FiniteLocalGL F (r + 1) v) {f : S.Space}
    (hf : f ∈ S.defectCore v s) : S.localRepresentation v h f ∈ S.defectCore v s := by
  intro g i
  have key := hf (g * h) i
  rw [← S.localRepresentation_mul_apply v g h f] at key
  exact key

theorem mem_defectCore_of_commute (A : Module.End ℂ S.Space)
    (hA : ∀ g f, A (S.localRepresentation v g f) = S.localRepresentation v g (A f))
    {f : S.Space} (hf : f ∈ S.defectCore v s) : A f ∈ S.defectCore v s :=
  fun g i => (congrArg (S.standardDefect v s i) (hA g f).symm).trans
    ((S.standardDefect_commute v s A hA i _).trans ((congrArg A (hf g i)).trans A.map_zero))

theorem finiteRepresentation_mem_defectCore (d : FiniteAdelicGL F (r + 1)) {f : S.Space}
    (hf : f ∈ S.defectCore v s) : S.finiteRepresentation d f ∈ S.defectCore v s := by
  let e := localInclusion F (r + 1) v (localProjection F (r + 1) v d)
  have hA : ∀ g f, S.finiteRepresentation (d * e⁻¹) (S.localRepresentation v g f) =
      S.localRepresentation v g (S.finiteRepresentation (d * e⁻¹) f) := fun g f =>
    (congrArg (fun x => S.finiteRepresentation (d * e⁻¹) x) (S.localRepresentation_apply v g f)).trans
      ((S.finiteRepresentation_mul_apply _ _ f).trans
        ((congrArg (fun x => S.finiteRepresentation x f) (commute_localInclusion_away v d g)).trans
          ((S.finiteRepresentation_mul_apply _ _ f).symm.trans
            (S.localRepresentation_apply v g _).symm)))
  have h : S.finiteRepresentation d f =
      S.finiteRepresentation (d * e⁻¹) (S.localRepresentation v (localProjection F (r + 1) v d) f) :=
    (congrArg (fun x => S.finiteRepresentation x f) (inv_mul_cancel_right d e).symm).trans
      ((S.finiteRepresentation_mul_apply _ _ f).symm.trans
        (congrArg (fun x => S.finiteRepresentation (d * e⁻¹) x)
          (S.localRepresentation_apply v _ f).symm))
  exact (congrArg (fun x => x ∈ S.defectCore v s) h).mpr
    (S.mem_defectCore_of_commute v s _ hA (S.localRepresentation_mem_defectCore v s _ hf))

theorem compactRepresentation_mem_defectCore (k : standardInfiniteCompact F (r + 1))
    {f : S.Space} (hf : f ∈ S.defectCore v s) :
    S.compactRepresentation k f ∈ S.defectCore v s :=
  S.mem_defectCore_of_commute v s _
    (fun g f => (S.finiteRepresentation_compactRepresentation (localInclusion F (r + 1) v g)
      k f).symm) hf

theorem envelopingAction_mem_defectCore (a : ArchimedeanGL.EnvelopingAlgebra F (r + 1))
    {f : S.Space} (hf : f ∈ S.defectCore v s) :
    S.envelopingAction a f ∈ S.defectCore v s :=
  S.mem_defectCore_of_commute v s _
    (fun g f => (S.finiteRepresentation_envelopingAction (localInclusion F (r + 1) v g)
      a f).symm) hf

/-- A nonzero local subspace of the form image with spherical spectrum `s` produces a
nonzero vector of the defect core. -/
theorem defectCore_ne_bot (L : LocalRealization F (r + 1) v)
    (hL : L ≤ S.toFiniteRealization.toLocal F (r + 1) v) (hne : L ≠ ⊥)
    (hs : L.HasSphericalHeckeSpectrum s) : S.defectCore v s ≠ ⊥ := by
  have hne' : L.toSubmodule ≠ ⊥ := fun h => hne (Subrepresentation.toSubmodule_injective h)
  obtain ⟨f₀, hf₀, hf₀ne⟩ := (Submodule.ne_bot_iff _).mp hne'
  obtain ⟨t, rfl⟩ := hL hf₀
  have ht : t ∈ S.defectCore v s := by
    intro g i
    let z : L.Space := L.representation g ⟨S.formInclusion t, hf₀⟩
    have hz : S.localFormInclusion v (S.localRepresentation v g t) = L.inclusion z := by
      rw [Representation.IntertwiningMap.isIntertwining _ _ (S.localFormInclusion v)]
      rfl
    have h₁ := PairedHecke.heckeDefect_intertwiner (CompletionPadic.padicField v)
      (S.localRepresentation v) (S.localRepresentation_isSmooth_canonical v)
      (automorphicLocalRightAction F (r + 1) v)
      (automorphicLocalRightAction_isSmooth_canonical F v (r + 1)) (S.localFormInclusion v)
      (standardHeckeElement (CompletionPadic.padicField v) r i)
      (standardHeckeScalar (CompletionPadic.padicField v) s i) (S.localRepresentation v g t)
    have h₂ := PairedHecke.heckeDefect_intertwiner (CompletionPadic.padicField v)
      L.representation L.isSmooth_canonical
      (automorphicLocalRightAction F (r + 1) v)
      (automorphicLocalRightAction_isSmooth_canonical F v (r + 1)) L.inclusion
      (standardHeckeElement (CompletionPadic.padicField v) r i)
      (standardHeckeScalar (CompletionPadic.padicField v) s i) z
    have h₃ := PairedHecke.heckeDefect_eq_zero (CompletionPadic.padicField v)
      L.representation L.isSmooth_canonical
      (standardHeckeElement (CompletionPadic.padicField v) r i)
      (standardHeckeScalar (CompletionPadic.padicField v) s i) (fun x => hs.2 i x) z
    have key : S.localFormInclusion v (S.standardDefect v s i (S.localRepresentation v g t)) =
        S.localFormInclusion v 0 :=
      h₁.trans ((congrArg _ hz).trans (h₂.symm.trans ((congrArg L.inclusion h₃).trans
        (L.inclusion.toLinearMap.map_zero.trans
          (S.localFormInclusion v).toLinearMap.map_zero.symm))))
    exact S.formInclusion_injective key
  intro hbot
  have ht0 : t = 0 := (Submodule.eq_bot_iff _).mp hbot t ht
  exact hf₀ne ((congrArg S.formInclusion ht0).trans S.formInclusion.toLinearMap.map_zero)

/-- In an irreducible realization, a nonzero local component inside the form image with
spherical spectrum `s` forces the defect core to be the whole space. -/
theorem defectCore_eq_top (hS : S.IsIrreducible) (L : LocalRealization F (r + 1) v)
    (hL : L ≤ S.toFiniteRealization.toLocal F (r + 1) v) (hne : L ≠ ⊥)
    (hs : L.HasSphericalHeckeSpectrum s) : S.defectCore v s = ⊤ :=
  S.eq_top_of_generatorStable hS _
    (fun d _ hf => S.finiteRepresentation_mem_defectCore v s d hf)
    (fun k _ hf => S.compactRepresentation_mem_defectCore v s k hf)
    (fun a _ hf => S.envelopingAction_mem_defectCore v s a hf)
    (S.defectCore_ne_bot v s L hL hne hs)

/-- A spherical vector in the defect core has the standard Hecke scalars of `s`. -/
theorem corner_eq_smul_of_mem_defectCore
    (a : fixedVectors (S.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup)
    (ha : (a : S.Space) ∈ S.defectCore v s) (i : Fin (r + 2)) :
    PairedHecke.corner (CompletionPadic.padicField v) (S.localRepresentation v)
        (S.localRepresentation_isSmooth_canonical v)
        (standardHeckeElement (CompletionPadic.padicField v) r i) a =
      standardHeckeScalar (CompletionPadic.padicField v) s i • a := by
  apply PairedHecke.corner_eq_smul_of_heckeDefect
  have e : S.localRepresentation v 1 (a : S.Space) = a :=
    LinearMap.congr_fun (map_one (S.localRepresentation v)) (a : S.Space)
  exact (congrArg (S.standardDefect v s i) e).symm.trans (ha 1 i)

/-- In an irreducible realization, the spectrum of one nonzero local component inside the
form image holds on every spherical vector of the whole local restriction. -/
theorem corner_eq_smul_of_localComponent (hS : S.IsIrreducible)
    (L : LocalRealization F (r + 1) v)
    (hL : L ≤ S.toFiniteRealization.toLocal F (r + 1) v) (hne : L ≠ ⊥)
    (hs : L.HasSphericalHeckeSpectrum s)
    (a : fixedVectors (S.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup)
    (i : Fin (r + 2)) :
    PairedHecke.corner (CompletionPadic.padicField v) (S.localRepresentation v)
        (S.localRepresentation_isSmooth_canonical v)
        (standardHeckeElement (CompletionPadic.padicField v) r i) a =
      standardHeckeScalar (CompletionPadic.padicField v) s i • a := by
  have htop := S.defectCore_eq_top v s hS L hL hne hs
  have ha : (a : S.Space) ∈ S.defectCore v s := by
    rw [htop]
    exact Submodule.mem_top
  exact S.corner_eq_smul_of_mem_defectCore v s a ha i

end Defect

section Spherical

variable (v : FinitePlace F)

local instance contraSphericalTopology (m : ℕ) : TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance contraSphericalTopologicalGroup (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance contraSphericalT2 (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance contraSphericalMeasurable (m : ℕ) : MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance contraSphericalBorel (m : ℕ) : BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

variable {r : ℕ} (S : OperatorRealization F (r + 1))

/-- A vector of the realization whose form is a spherical vector of a local component is
itself spherical for the local restriction. -/
theorem mem_spherical_of_formInclusion (L : LocalRealization F (r + 1) v) (f₀ : L.Space)
    (hf₀ : f₀ ∈ L.SphericalVectors) (b : S.Space) (hb : S.formInclusion b = f₀) :
    b ∈ fixedVectors (S.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup := fun k =>
  S.formInclusion_injective
    ((Representation.IntertwiningMap.isIntertwining _ _ (S.localFormInclusion v)
      (k : FiniteLocalGL F (r + 1) v) b).trans
      ((congrArg (automorphicLocalRightAction F (r + 1) v (k : FiniteLocalGL F (r + 1) v))
        hb).trans ((congrArg Subtype.val (hf₀ k)).trans hb.symm)))

/-- A local component inside the form image with a nonzero spherical vector produces a
nonzero spherical vector of the whole local restriction. -/
theorem exists_spherical_ne_zero_of_le (L : LocalRealization F (r + 1) v)
    (hL : L ≤ S.toFiniteRealization.toLocal F (r + 1) v) (h : L.SphericalVectors ≠ ⊥) :
    ∃ b : fixedVectors (S.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup, b ≠ 0 :=
  -- Term mode: `obtain` against this subtype-valued goal exhausts `whnf`.
  ((Submodule.ne_bot_iff _).mp h).elim fun f₀ hf₀ =>
    Exists.elim (hL f₀.property) fun b hb =>
      ⟨⟨b, S.mem_spherical_of_formInclusion v L f₀ hf₀.1 b hb⟩, fun h0 =>
        hf₀.2 (Subtype.ext (hb.symm.trans ((congrArg S.formInclusion
          (congrArg Subtype.val h0 : b = 0)).trans S.formInclusion.toLinearMap.map_zero)))⟩

/-- If `S'` realizes the contragredient of `S` and both satisfy spherical spectra on all
spherical vectors at `v`, with a nonzero spherical vector in `S'`, then the spectra are
inverse. -/
theorem eq_map_inv_of_isContragredientOf {S' : OperatorRealization F (r + 1)}
    (h : S'.IsContragredientOf S) (s s' : Eigenvalues (r + 1))
    (hs : ∀ (a : fixedVectors (S.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (i : Fin (r + 2)),
      PairedHecke.corner (CompletionPadic.padicField v) (S.localRepresentation v)
          (S.localRepresentation_isSmooth_canonical v)
          (standardHeckeElement (CompletionPadic.padicField v) r i) a =
        standardHeckeScalar (CompletionPadic.padicField v) s i • a)
    (hs' : ∀ (b : fixedVectors (S'.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (i : Fin (r + 2)),
      PairedHecke.corner (CompletionPadic.padicField v) (S'.localRepresentation v)
          (S'.localRepresentation_isSmooth_canonical v)
          (standardHeckeElement (CompletionPadic.padicField v) r i) b =
        standardHeckeScalar (CompletionPadic.padicField v) s' i • b)
    (b : fixedVectors (S'.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup) (hb : b ≠ 0) :
    s' = s.map fun z => z⁻¹ := by
  obtain ⟨B, hBinv, -, hinj, -⟩ := h
  have hB : ∀ (g : FiniteLocalGL F (r + 1) v) x y,
      B (S.localRepresentation v g x) (S'.localRepresentation v g y) = B x y :=
    fun g x y => hBinv.1 (localInclusion F (r + 1) v g) x y
  have hBb : B.flip (b : S'.Space) ≠ 0 := fun h0 =>
    hb (Subtype.ext (hinj (h0.trans (map_zero B.flip).symm)))
  obtain ⟨y, hy⟩ : ∃ y, B y b ≠ 0 := by
    by_contra! hall
    exact hBb (LinearMap.ext hall)
  let a := PairedHecke.sphericalProjection (CompletionPadic.padicField v)
    (S.localRepresentation v) (S.localRepresentation_isSmooth_canonical v) y
  have e := PairedHecke.pairing_sphericalProjection (CompletionPadic.padicField v)
    (S.localRepresentation v) (S.localRepresentation_isSmooth_canonical v)
    (S'.localRepresentation v) B hB y b
  have hab : B a b ≠ 0 := fun h0 => hy (e.symm.trans h0)
  exact PairedHecke.eq_map_inv_of_pairing (CompletionPadic.padicField v)
    (S.localRepresentation v) (S.localRepresentation_isSmooth_canonical v)
    (S'.localRepresentation v) (S'.localRepresentation_isSmooth_canonical v)
    B hB a b s s' (hs a) (hs' b) hab

end Spherical

end OperatorRealization

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} {T : CuspidalOperatorRealization F r}
variable (P : CuspidalSpectralPresentation.{uF, uV} T) (v : FinitePlace F)

local instance contraPresentationTopology (m : ℕ) : TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance contraPresentationTopologicalGroup (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance contraPresentationT2 (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance contraPresentationMeasurable (m : ℕ) : MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance contraPresentationBorel (m : ℕ) : BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

/-- The local component of a presentation lies in the form image of the realization. -/
theorem localComponent_le_image :
    P.localComponent v ≤ T.realization.toFiniteRealization.toLocal F (r + 1) v :=
  fun _ hf => P.finiteSlice.le_image (P.presentation.localComponent_le _ v hf)

/-- Away from the exceptional set, every spherical vector of the whole realization, for
the local restriction at `v`, has the standard Hecke scalars of the presented spectrum. -/
theorem corner_eq_smul (hv : v ∉ P.exceptional)
    (a : fixedVectors (T.realization.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup)
    (i : Fin (r + 2)) :
    PairedHecke.corner (CompletionPadic.padicField v) (T.realization.localRepresentation v)
        (T.realization.localRepresentation_isSmooth_canonical v)
        (standardHeckeElement (CompletionPadic.padicField v) r i) a =
      standardHeckeScalar (CompletionPadic.padicField v) (P.spectralSystem.eigenvalues v hv) i •
        a :=
  T.realization.corner_eq_smul_of_localComponent v _ T.irreducible (P.localComponent v)
    (P.localComponent_le_image v) (P.localComponent_ne_bot v) (P.hasSpectrum v hv) a i

/-- Away from the exceptional set, the whole local restriction has a nonzero spherical
vector. -/
theorem exists_spherical_ne_zero (hv : v ∉ P.exceptional) :
    ∃ b : fixedVectors (T.realization.localRepresentation v)
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup, b ≠ 0 :=
  T.realization.exists_spherical_ne_zero_of_le v (P.localComponent v)
    (P.localComponent_le_image v) (P.hasSpectrum v hv).1

end CuspidalSpectralPresentation

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- If `T'` realizes the contragredient of `T`, then outside the exceptional sets of two
presentations, the spectrum of `T'` is the inverse of that of `T`. -/
theorem eigenvalues_eq_map_inv_of_isContragredientOf (T T' : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uV} T) (P' : CuspidalSpectralPresentation.{uF, uW} T')
    (h : T'.realization.IsContragredientOf T.realization) (v : FinitePlace F)
    (hv : v ∉ P.exceptional) (hv' : v ∉ P'.exceptional) :
    P'.spectralSystem.eigenvalues v hv' =
      (P.spectralSystem.eigenvalues v hv).map fun z => z⁻¹ := by
  obtain ⟨b, hb⟩ := P'.exists_spherical_ne_zero v hv'
  exact T.realization.eq_map_inv_of_isContragredientOf v h _ _ (P.corner_eq_smul v hv)
    (P'.corner_eq_smul v hv') b hb

end CuspidalOperatorRealization

end Langlands.Automorphic
