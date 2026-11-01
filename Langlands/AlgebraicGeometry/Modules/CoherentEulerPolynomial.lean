import Langlands.AlgebraicGeometry.Modules.CoherentEulerDifference
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # Euler polynomials by induction on coherent support -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules QuasicoherentLocal

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    [IsNoetherian X] [X.IsSeparated]

/-- The support-height bound kills the corresponding difference of the actual Euler sequence. -/
theorem iterate_fwdDiff_coherentEulerSequence_eq_zero_of_height (e : ℕ) :
    ∀ (Z : Closeds X) (M : X.Modules) [M.IsQuasicoherent]
      (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X),
      VanishesOn M Z.compl →
      (∀ T : IrreducibleCloseds X, (T : Set X) ⊆ Z → height T < e) →
      (fwdDiff 1)^[e] (coherentEulerSequence f M hM L) = 0 := by
  induction e with
  | zero =>
    intro Z M _ hM L hMZ hZ
    exact coherentEulerSequence_zero f M hM L
      (HasSupportDimensionLT.isZero ⟨Z, hMZ, hZ⟩)
  | succ d ih =>
    intro Z
    induction Z using WellFoundedLT.induction with
    | _ Z IH =>
      intro M _ hM L hMZ hZ
      by_cases hZe : (Z : Set X) = ∅
      · have hzero : IsZero M := NoetherianVanishing.isZero_of_vanishesOn_top
          (hMZ.mono (fun x _ hx => by
            simp only [hZe, Set.mem_empty_iff_false] at hx))
        rw [coherentEulerSequence_zero f M hM L hzero, iterate_fwdDiff_zero]
      obtain ⟨T, O, hTZ, ⟨η, hηO, hηZ⟩, hOT⟩ :=
        NoetherianVanishing.exists_irreducibleCloseds_inter_subset Z
          (Set.nonempty_iff_ne_empty.2 hZe)
      obtain ⟨W, hηW, ⟨t⟩⟩ := L.property η
      obtain ⟨V, hV, hηV, hVOW⟩ :=
        (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
          (show η ∈ O ⊓ W from ⟨hηO, hηW⟩)
      change X.Opens at V
      have hVO : V ≤ O := hVOW.trans inf_le_left
      let tV : L.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).app L.obj ≪≫
          Picard.pullbackTrivializationOfLE (hVOW.trans inf_le_right) L.obj t
      have := isAffineHom_affineOpen_ι hV
      let J := (Scheme.Modules.pushforward V.ι).obj (M.restrict V.ι)
      have : J.IsQuasicoherent :=
        isQuasicoherent_pushforward V.ι (M.restrict V.ι)
      let φ : M ⟶ J := unitMap V.ι M
      let p := factorThruImage φ
      let i := image.ι φ
      have := isQuasicoherent_image φ
      have := isQuasicoherent_kernel p
      have hI : HasFiniteAffineSections (image φ) := hM.of_epi p
      have hK : HasFiniteAffineSections (kernel p) := hM.kernel p
      -- The kernel has support in a proper closed subset of the original support.
      let Z' : Closeds X :=
        ⟨(Z : Set X) ∩ (V : Set X)ᶜ, Z.isClosed.inter V.isOpen.isClosed_compl⟩
      have hZ'Z : Z' < Z := by
        refine lt_of_le_of_ne (fun x hx => hx.1) (fun h => ?_)
        have : η ∈ (Z' : Set X) := by rw [h]; exact hηZ
        exact this.2 hηV
      have eK : kernel φ ≅ kernel p :=
        (kernelIsoOfEq (image.fac φ)).symm ≪≫ kernelCompMono p i
      have hKsupp : VanishesOn (kernel p) Z'.compl := by
        have h1 : VanishesOn (kernel φ) (Z.compl ⊔ V) :=
          (hMZ.kernel φ).sup
            ((Scheme.Opens.opensRange_ι V) ▸ vanishesOn_kernel_unitMap V.ι M)
        refine (h1.mono ?_).of_iso eK
        intro x hx
        by_cases hxV : x ∈ V
        · exact Or.inr hxV
        · exact Or.inl (fun hxZ => hx ⟨hxZ, hxV⟩)
      have hKzero := IH Z' hZ'Z (kernel p) hK L hKsupp
        (fun S hS => hZ S (hS.trans (fun x hx => hx.1)))
      -- The image and its line-bundle twist are both supported on T.
      let Tc : X.Opens := ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩
      have hJT : VanishesOn J Tc := by
        refine vanishesOn_pushforward_restrict V.ι M hMZ (fun A hA => ?_)
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
        rintro x ⟨hxV, hxA⟩ hxZ
        exact hA hxA (hOT ⟨hVO hxV, hxZ⟩)
      have hIT : VanishesOn (image φ) Tc := hJT.of_mono i
      have := isQuasicoherent_tensor_lineBundle (image φ) L.obj L.property
      have hNT : VanishesOn (tensorObj (image φ) L.obj) Tc := by
        apply VanishesOn.of_stalkSupport_subset_compl
        rw [stalkSupport_tensor_lineBundle (image φ) L.obj L.property]
        exact hIT.stalkSupport_subset_compl
      have hT : height T ≤ d := by
        have h := hZ T hTZ
        push_cast at h
        exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).1 h
      have hD := iterate_fwdDiff_sub_of_graph f d
        (fun A _ hA L hA' => by
          obtain ⟨S, hAS, hS⟩ := hA'
          exact ih S A hA L hAS hS)
        (image φ) (tensorObj (image φ) L.obj) hI (hI.tensor_lineBundle L.property)
        L T hT V hV ⟨η, hOT ⟨hηO, hηZ⟩, hηV⟩ hIT hNT
        (tensorRestrictionTrivialization (image φ) L.obj V tV)
      have hshift :
          coherentEulerSequence f (tensorObj (image φ) L.obj)
              (hI.tensor_lineBundle L.property) L -
            coherentEulerSequence f (image φ) hI L =
          fwdDiff 1 (coherentEulerSequence f (image φ) hI L) := by
        ext n
        change coherentEulerSequence f (tensorObj (image φ) L.obj) _ L n -
          coherentEulerSequence f (image φ) hI L n = _
        rw [coherentEulerSequence_shift]
        rfl
      have hIzero :
          (fwdDiff 1)^[d + 1] (coherentEulerSequence f (image φ) hI L) = 0 := by
        rw [Function.iterate_succ_apply, ← hshift]
        exact hD
      let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
      have hadd := coherentEulerSequence_add f S hS hK hM hI L
      change coherentEulerSequence f M hM L = _ at hadd
      rw [hadd, fwdDiff_iter_add, hKzero, hIzero, add_zero]

/-- A coherent module's support bound implies vanishing of that iterated Euler difference. -/
theorem hasVanishingEulerDifference_of_support (e : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L : Picard.LineBundle X) (h : HasSupportDimensionLT M e) :
    HasVanishingEulerDifference f M hM L e := by
  obtain ⟨Z, hMZ, hZ⟩ := h
  exact iterate_fwdDiff_coherentEulerSequence_eq_zero_of_height f e Z M hM L hMZ hZ

/-- The Newton polynomial of the actual coherent Euler sequence. -/
def coherentEulerPolynomial (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (d : ℕ) :
    Polynomial ℚ :=
  Langlands.Algebra.RationalPolynomial.newtonPolynomial (coherentEulerSequence f M hM L) d

/-- The Euler polynomial is exact at every natural argument under the support bound. -/
theorem coherentEulerPolynomial_eval (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (d : ℕ)
    (h : HasSupportDimensionLT M (d + 1)) (n : ℕ) :
    (coherentEulerPolynomial f M hM L d).eval (n : ℚ) = coherentEulerSequence f M hM L n :=
  Langlands.Algebra.RationalPolynomial.newtonPolynomial_eval_eq _ d
    (hasVanishingEulerDifference_of_support f (d + 1) M hM L h) n

omit [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated] in
/-- The Euler polynomial has degree at most the given support-dimension bound. -/
theorem coherentEulerPolynomial_natDegree_le (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (d : ℕ) :
    (coherentEulerPolynomial f M hM L d).natDegree ≤ d :=
  Langlands.Algebra.RationalPolynomial.newtonPolynomial_natDegree_le _ d

/-- A dense affine identification on irreducible support preserves the top Euler difference. -/
theorem iterate_fwdDiff_sub_of_irreducible (d : ℕ)
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N)
    (L : Picard.LineBundle X) (T : IrreducibleCloseds X) (hT : height T ≤ d)
    (U : X.Opens) (hU : IsAffineOpen U) (hTU : ((T : Set X) ∩ U).Nonempty)
    (hMT : VanishesOn M ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hNT : VanishesOn N ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (i : N.restrict U.ι ≅ M.restrict U.ι) :
    (fwdDiff 1)^[d] (coherentEulerSequence f N hN L - coherentEulerSequence f M hM L) = 0 :=
  iterate_fwdDiff_sub_of_graph f d
    (fun A _ hA L h => hasVanishingEulerDifference_of_support f d A hA L h)
    M N hM hN L T hT U hU hTU hMT hNT i

end Langlands.AlgebraicGeometry.Modules.DerivedSections
