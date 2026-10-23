import Langlands.Representation.Jacquet.CanonicalLiftGroupTransportStatement

noncomputable section

namespace Langlands.Jacquet

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable (e : H ≃ₜ* G) (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (hKL : K.toSubgroup.map e.toMonoidHom = L.toSubgroup)

include hKL

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Equality of the actual subgroup orbits, on every ambient vector. -/
theorem orbit_groupTransport (v : V) :
    Compact.orbit ((ρ.comp e.toMonoidHom).comp K.toSubgroup.subtype) v =
      Compact.orbit (ρ.comp L.toSubgroup.subtype) v := by
  ext w
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨e k, hKL ▸ ⟨k, k.property, rfl⟩⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    have hl : (l : G) ∈ K.toSubgroup.map e.toMonoidHom := hKL.symm ▸ l.property
    obtain ⟨k, hk, heq⟩ := hl
    exact ⟨⟨k, hk⟩, by change ρ (e k) v = ρ l v; exact congrArg (fun x => ρ x v) heq⟩

/-- Normalized average equality as endomorphisms of the actual carrier. -/
theorem averageMap_groupTransport :
    Compact.averageMap (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK =
    Compact.averageMap ρ hρ L hL := by
  ext v
  change Compact.orbitMean _ v = Compact.orbitMean _ v
  unfold Compact.orbitMean
  rw [orbit_groupTransport e ρ K L hKL v]

/-- Pointwise average transport has no fixedness hypothesis on the vector. -/
theorem averageMap_groupTransport_apply (v : V) :
    Compact.averageMap (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK v =
    Compact.averageMap ρ hρ L hL v :=
  LinearMap.congr_fun (averageMap_groupTransport e ρ hρ K hK L hL hKL) v

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Equality of the two actual fixed submodules of the same carrier. -/
theorem fixedVectors_groupTransport :
    fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup =
      fixedVectors ρ L.toSubgroup := by
  rw [fixedVectors_comp_mulEquiv ρ e.toMulEquiv]
  congr 1
  rw [← hKL]
  ext g
  constructor
  · intro hg
    exact ⟨e.symm g, hg, e.apply_symm_apply g⟩
  · rintro ⟨h, hh, rfl⟩
    simpa using hh

/-- The identity on ambient vectors as an equivalence of fixed submodules. -/
def fixedVectorsGroupTransportEquiv :
    fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup ≃ₗ[ℂ]
      fixedVectors ρ L.toSubgroup :=
  LinearEquiv.ofEq _ _ (fixedVectors_groupTransport e ρ K L hKL)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
theorem fixedVectorsGroupTransportEquiv_apply
    (v : fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup) :
    (fixedVectorsGroupTransportEquiv e ρ K L hKL v : V) = v := rfl

/-- Pointwise conjugacy of the actual compressed actions. -/
theorem compressedAction_groupTransport (g : H)
    (v : fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup) :
    fixedVectorsGroupTransportEquiv e ρ K L hKL
      (compressedAction (ρ.comp e.toMonoidHom)
        (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g v) =
    compressedAction ρ hρ L hL (e g)
      (fixedVectorsGroupTransportEquiv e ρ K L hKL v) := by
  apply Subtype.ext
  exact averageMap_groupTransport_apply e ρ hρ K hK L hL hKL (ρ (e g) v)

/-- The same conjugacy for every natural power, including zero. -/
theorem compressedAction_pow_groupTransport (g : H) (r : ℕ)
    (v : fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup) :
    fixedVectorsGroupTransportEquiv e ρ K L hKL
      ((compressedAction (ρ.comp e.toMonoidHom)
        (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g ^ r) v) =
    (compressedAction ρ hρ L hL (e g) ^ r)
      (fixedVectorsGroupTransportEquiv e ρ K L hKL v) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [compressedAction_groupTransport e ρ hρ K hK L hL hKL, ih]

/-- Stable-image membership under the actual fixed-space identification. -/
theorem mem_stableImage_groupTransport (g : H)
    (v : fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup) :
    v ∈ stableImage (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g ↔
    fixedVectorsGroupTransportEquiv e ρ K L hKL v ∈ stableImage ρ hρ L hL (e g) := by
  rw [mem_stableImage, mem_stableImage]
  constructor
  · intro hv r
    obtain ⟨w, hw⟩ := hv r
    refine ⟨fixedVectorsGroupTransportEquiv e ρ K L hKL w, ?_⟩
    rw [← compressedAction_pow_groupTransport e ρ hρ K hK L hL hKL, hw]
  · intro hv r
    obtain ⟨w, hw⟩ := hv r
    obtain ⟨w, rfl⟩ := (fixedVectorsGroupTransportEquiv e ρ K L hKL).surjective w
    refine ⟨w, (fixedVectorsGroupTransportEquiv e ρ K L hKL).injective ?_⟩
    rw [compressedAction_pow_groupTransport e ρ hρ K hK L hL hKL, hw]

/-- The same-carrier membership formulation of the published clause. -/
theorem stableImage_groupTransport (g : H) (v : V)
    (hvK : v ∈ fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup)
    (hvL : v ∈ fixedVectors ρ L.toSubgroup) :
    (⟨v, hvK⟩ ∈ stableImage (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g) ↔
    (⟨v, hvL⟩ ∈ stableImage ρ hρ L hL (e g)) :=
  mem_stableImage_groupTransport e ρ hρ K hK L hL hKL g ⟨v, hvK⟩

/-- Identification of the actual stable-image carriers. -/
def stableImageGroupTransportEquiv (g : H) :
    stableImage (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g ≃ₗ[ℂ]
    stableImage ρ hρ L hL (e g) :=
  (fixedVectorsGroupTransportEquiv e ρ K L hKL).ofSubmodules _ _ (by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_stableImage_groupTransport e ρ hρ K hK L hL hKL g w).mp hw
    · intro hv
      obtain ⟨w, rfl⟩ := (fixedVectorsGroupTransportEquiv e ρ K L hKL).surjective v
      exact ⟨w, (mem_stableImage_groupTransport e ρ hρ K hK L hL hKL g w).mpr hv, rfl⟩)

/-- Stable-image transport preserves pointwise inclusion into the ambient module. -/
@[simp]
theorem stableImageToRepresentation_groupTransport (g : H)
    (v : stableImage (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g) :
    stableImageToRepresentation ρ hρ L hL (e g)
      (stableImageGroupTransportEquiv e ρ hρ K hK L hL hKL g v) =
    stableImageToRepresentation (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g v := rfl

/-- Transport of the actual supremum of all power kernels. -/
theorem powerKernelSup_map_groupTransport (g : H) :
    (powerKernelSup (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g).map
        (fixedVectorsGroupTransportEquiv e ρ K L hKL).toLinearMap =
    powerKernelSup ρ hρ L hL (e g) := by
  unfold powerKernelSup
  rw [Submodule.map_iSup]
  congr 1
  funext r
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change (compressedAction ρ hρ L hL (e g) ^ r)
      (fixedVectorsGroupTransportEquiv e ρ K L hKL v) = 0
    rw [← compressedAction_pow_groupTransport e ρ hρ K hK L hL hKL]
    rw [LinearMap.mem_ker.mp hv, map_zero]
  · intro hw
    obtain ⟨v, rfl⟩ := (fixedVectorsGroupTransportEquiv e ρ K L hKL).surjective w
    refine ⟨v, ?_, rfl⟩
    apply (fixedVectorsGroupTransportEquiv e ρ K L hKL).injective
    rw [map_zero, compressedAction_pow_groupTransport e ρ hρ K hK L hL hKL]
    exact hw

omit hKL

variable (N M : Subgroup H) (N' M' : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (hM'N' : M' ≤ Subgroup.normalizer N')
    (hN : N.map e.toMonoidHom = N') (hM : M.map e.toMonoidHom = M')

/-- The existing coinvariant equivalence with its target rewritten to the image subgroup. -/
def coinvariantsGroupTransportEquiv :
    Coinvariants (ρ.comp e.toMonoidHom) N ≃ₗ[ℂ] Coinvariants ρ N' :=
  hN ▸ coinvariantsMapEquiv ρ e.toMonoidHom N

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
theorem coinvariantsGroupTransportEquiv_mk (v : V) :
    coinvariantsGroupTransportEquiv e ρ N N' hN (mk (ρ.comp e.toMonoidHom) N v) =
      mk ρ N' v := by
  subst N'
  exact coinvariantsMapEquiv_mk ρ e.toMonoidHom N v

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Transport of the actual unnormalized descended Levi action. -/
theorem action_groupTransport (m : M) (m' : M') (hm : e m = m')
    (v : Coinvariants (ρ.comp e.toMonoidHom) N) :
    coinvariantsGroupTransportEquiv e ρ N N' hN
      (action (ρ.comp e.toMonoidHom) N M hMN m v) =
    action ρ N' M' hM'N' m' (coinvariantsGroupTransportEquiv e ρ N N' hN v) := by
  obtain ⟨v, rfl⟩ := mk_surjective (ρ.comp e.toMonoidHom) N v
  rw [action_mk, coinvariantsGroupTransportEquiv_mk,
    coinvariantsGroupTransportEquiv_mk, action_mk]
  exact congrArg (mk ρ N') (congrArg (fun x => ρ x v) hm)

include hKL hM hN

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The quotient equivalence identifies exactly the two fixed Jacquet codomains. -/
theorem fixedJacquet_mem_groupTransport (v : Coinvariants (ρ.comp e.toMonoidHom) N) :
    v ∈ fixedVectors (action (ρ.comp e.toMonoidHom) N M hMN)
      (K.toSubgroup.comap M.subtype) ↔
    coinvariantsGroupTransportEquiv e ρ N N' hN v ∈
      fixedVectors (action ρ N' M' hM'N') (L.toSubgroup.comap M'.subtype) := by
  constructor
  · intro hv m'
    have hm' : (m'.val.val : G) ∈ M.map e.toMonoidHom := hM.symm ▸ m'.val.property
    obtain ⟨m, hm, heq⟩ := hm'
    have hk : m ∈ K.toSubgroup := by
      have hl : e m ∈ K.toSubgroup.map e.toMonoidHom := by
        rw [hKL]
        exact heq.symm ▸ m'.property
      obtain ⟨k, hk, he⟩ := hl
      exact e.injective he ▸ hk
    change action ρ N' M' hM'N' m'.val
      (coinvariantsGroupTransportEquiv e ρ N N' hN v) = _
    rw [← action_groupTransport e ρ N M N' M' hMN hM'N' hN ⟨m, hm⟩ m'.val heq]
    exact congrArg (coinvariantsGroupTransportEquiv e ρ N N' hN) (hv ⟨⟨m, hm⟩, hk⟩)
  · intro hv m
    let m' : M' := ⟨e m.val.val, hM ▸ ⟨m.val.val, m.val.property, rfl⟩⟩
    have hk : m'.val ∈ L.toSubgroup := hKL ▸ ⟨m.val.val, m.property, rfl⟩
    apply (coinvariantsGroupTransportEquiv e ρ N N' hN).injective
    exact (action_groupTransport e ρ N M N' M' hMN hM'N' hN m.val m' rfl v).trans
      (hv ⟨m', hk⟩)

/-- Restriction of the existing quotient equivalence to the actual fixed codomains. -/
def fixedJacquetGroupTransportEquiv :
    fixedVectors (action (ρ.comp e.toMonoidHom) N M hMN)
      (K.toSubgroup.comap M.subtype) ≃ₗ[ℂ]
    fixedVectors (action ρ N' M' hM'N') (L.toSubgroup.comap M'.subtype) :=
  (coinvariantsGroupTransportEquiv e ρ N N' hN).ofSubmodules _ _ (by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (fixedJacquet_mem_groupTransport e ρ K L hKL N M N' M' hMN hM'N' hN hM w).mp hw
    · intro hv
      obtain ⟨w, rfl⟩ := (coinvariantsGroupTransportEquiv e ρ N N' hN).surjective v
      exact ⟨w, (fixedJacquet_mem_groupTransport e ρ K L hKL N M N' M' hMN hM'N' hN hM w).mpr hv, rfl⟩)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
theorem fixedJacquetGroupTransportEquiv_apply
    (v : fixedVectors (action (ρ.comp e.toMonoidHom) N M hMN)
      (K.toSubgroup.comap M.subtype)) :
    (fixedJacquetGroupTransportEquiv e ρ K L hKL N M N' M' hMN hM'N' hN hM v :
      Coinvariants ρ N') = coinvariantsGroupTransportEquiv e ρ N N' hN v := rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Commutativity for the actual fixed-vector Jacquet maps. -/
theorem fixedJacquetMap_groupTransport
    (v : fixedVectors (ρ.comp e.toMonoidHom) K.toSubgroup) :
    fixedJacquetGroupTransportEquiv e ρ K L hKL N M N' M' hMN hM'N' hN hM
      (fixedJacquetMap (ρ.comp e.toMonoidHom) N M hMN K.toSubgroup v) =
    fixedJacquetMap ρ N' M' hM'N' L.toSubgroup
      (fixedVectorsGroupTransportEquiv e ρ K L hKL v) := by
  apply Subtype.ext
  exact coinvariantsGroupTransportEquiv_mk e ρ N N' hN v

/-- Pointwise commutativity for the actual stable-image quotient maps. -/
theorem stableImageJacquetMap_groupTransport (g : H)
    (v : stableImage (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g) :
    fixedJacquetGroupTransportEquiv e ρ K L hKL N M N' M' hMN hM'N' hN hM
      (stableImageJacquetMap (ρ.comp e.toMonoidHom)
        (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g N M hMN v) =
    stableImageJacquetMap ρ hρ L hL (e g) N' M' hM'N'
      (stableImageGroupTransportEquiv e ρ hρ K hK L hL hKL g v) := by
  apply Subtype.ext
  exact coinvariantsGroupTransportEquiv_mk e ρ N N' hN v.val.val

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The kernel of the actual restricted quotient map transports as a submodule. -/
theorem fixedJacquetMap_ker_map_groupTransport :
    (LinearMap.ker (fixedJacquetMap (ρ.comp e.toMonoidHom) N M hMN K.toSubgroup)).map
      (fixedVectorsGroupTransportEquiv e ρ K L hKL).toLinearMap =
    LinearMap.ker (fixedJacquetMap ρ N' M' hM'N' L.toSubgroup) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change fixedJacquetMap ρ N' M' hM'N' L.toSubgroup
      (fixedVectorsGroupTransportEquiv e ρ K L hKL v) = 0
    rw [← fixedJacquetMap_groupTransport e ρ K L hKL N M N' M' hMN hM'N' hN hM]
    rw [LinearMap.mem_ker.mp hv, map_zero]
  · intro hw
    obtain ⟨v, rfl⟩ := (fixedVectorsGroupTransportEquiv e ρ K L hKL).surjective w
    refine ⟨v, ?_, rfl⟩
    apply (fixedJacquetGroupTransportEquiv e ρ K L hKL N M N' M' hMN hM'N' hN hM).injective
    rw [map_zero, fixedJacquetMap_groupTransport e ρ K L hKL N M N' M' hMN hM'N' hN hM]
    exact hw

/-- The canonical-lift kernel equality transports in both directions. -/
theorem powerKernelSup_eq_ker_groupTransport (g : H) :
    (powerKernelSup (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g =
        LinearMap.ker (fixedJacquetMap (ρ.comp e.toMonoidHom) N M hMN K.toSubgroup)) ↔
    (powerKernelSup ρ hρ L hL (e g) =
        LinearMap.ker (fixedJacquetMap ρ N' M' hM'N' L.toSubgroup)) := by
  have hp := powerKernelSup_map_groupTransport e ρ hρ K hK L hL hKL g
  have hk := fixedJacquetMap_ker_map_groupTransport e ρ K L hKL N M N' M' hMN hM'N' hN hM
  constructor
  · intro h
    rw [← hp, h, hk]
  · intro h
    apply Submodule.map_injective_of_injective (fixedVectorsGroupTransportEquiv e ρ K L hKL).injective
    exact hp.trans (h.trans hk.symm)

/-- Bijectivity transports for the actual stable-image Jacquet maps. -/
theorem stableImageJacquetMap_bijective_groupTransport (g : H) :
    Function.Bijective (stableImageJacquetMap (ρ.comp e.toMonoidHom)
      (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g N M hMN) ↔
    Function.Bijective (stableImageJacquetMap ρ hρ L hL (e g) N' M' hM'N') := by
  let a := stableImageGroupTransportEquiv e ρ hρ K hK L hL hKL g
  let b := fixedJacquetGroupTransportEquiv e ρ K L hKL N M N' M' hMN hM'N' hN hM
  let f := stableImageJacquetMap (ρ.comp e.toMonoidHom)
    (isSmooth_comp e.toMonoidHom e.continuous hρ) K hK g N M hMN
  let f' := stableImageJacquetMap ρ hρ L hL (e g) N' M' hM'N'
  have hc (v) : b (f v) = f' (a v) :=
    stableImageJacquetMap_groupTransport e ρ hρ K hK L hL hKL N M N' M' hMN hM'N' hN hM g v
  change Function.Bijective f ↔ Function.Bijective f'
  constructor
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y hxy
      obtain ⟨x, rfl⟩ := a.surjective x
      obtain ⟨y, rfl⟩ := a.surjective y
      exact congrArg a (hi (b.injective (by simpa only [hc] using hxy)))
    · intro y
      obtain ⟨y, rfl⟩ := b.surjective y
      obtain ⟨x, rfl⟩ := hs y
      exact ⟨a x, (hc x).symm⟩
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y hxy
      apply a.injective
      apply hi
      rw [← hc, ← hc, hxy]
    · intro y
      obtain ⟨x, hx⟩ := hs (b y)
      obtain ⟨x, rfl⟩ := a.surjective x
      exact ⟨x, b.injective ((hc x).trans hx)⟩

omit hKL hM hN

/-- The complete independently published canonical Jacquet lift transport target. -/
theorem canonicalLiftGroupTransport :
    CanonicalLiftGroupTransportStatement (G := G) (H := H) (V := V) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun e ρ hρ K hK L hL hKL => averageMap_groupTransport e ρ hρ K hK L hL hKL
  · exact fun e ρ hρ K hK L hL hKL g v hvK hvL =>
      stableImage_groupTransport e ρ hρ K hK L hL hKL g v hvK hvL
  · exact fun e ρ hρ K hK L hL hKL g N M N' M' hMN hM'N' hN hM =>
      powerKernelSup_eq_ker_groupTransport e ρ hρ K hK L hL hKL N M N' M' hMN hM'N' hN hM g
  · exact fun e ρ hρ K hK L hL hKL g N M N' M' hMN hM'N' hN hM =>
      stableImageJacquetMap_bijective_groupTransport e ρ hρ K hK L hL hKL N M N' M' hMN hM'N' hN hM g

end Langlands.Jacquet
