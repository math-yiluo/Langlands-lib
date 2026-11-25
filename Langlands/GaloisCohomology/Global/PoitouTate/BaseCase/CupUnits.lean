import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.UnitsData

/-!
# Cup products of the Kummer classes with compact support

With the notation of `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.UnitsData`, this file
computes the cup product of the Kummer class with compact support `δ_c(e)` of a class
`e ∈ H_c¹(G_S, 𝒪_Sˣ; (K̄_vˣ)_v)` with a character `χ ∈ H¹(G_S, ℤ/n)`, after mapping
`μ_n → 𝒪_Sˣ`:

* `compactSupportMap_compactCupRes_kummerCompactδ`: `i_*(δ_c(e) ∪ χ) = e ∪ δχ`, `δχ ∈ H²(G_S, ℤ)` the
  Bockstein of `χ` and the cup product along the action `𝒪_Sˣ ⊗ ℤ → 𝒪_Sˣ` (the connecting maps of
  the Kummer sequence with compact support and of `0 → ℤ → ℤ → ℤ/n → 0` commute with cup products,
  `compactCup_compactSupportδ_add_compactCup_δ`);
* `exists_unitsData_cup_bock`: for the datum `(t, a)`, `e ∪ δχ` is the image under `localToCompact` of
  the family `(W|_{K_v} + a_v ∪ δχ_v)_v` for a `2`-cocycle `W` of `G_S` in `K_Sˣ` congruent to
  `t ^ {c_χ}` modulo `𝒪_Sˣ` (`c_χ` the integer cocycle `bockInt` of `δχ`): the cocycle of `e ∪ δχ`
  is `(σ(t)/t ∪ c_χ, (ι_v(t) a_v) ∪ c_χ)`; since `H³(G_S, 𝒪_Sˣ)` has no `n`-torsion for `n = ℓᵏ`
  (`eq_zero_of_cohomology_three_maximalSUnits`) the global part is the coboundary of a cochain `f`
  with values in `𝒪_Sˣ`, and `W = t ∪ c_χ - f`.
-/

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory Limits MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

section Abstract

variable {k : Type u} [CommRing k] {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ}
  {f : K ⟶ L} {f' : K' ⟶ L'} (μL : LeibnizPairing L N' L') (ρ : N ⟶ N')
  (μK : LeibnizPairing K N K')
  (hc : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
    (f'.f n).hom (μK.μ h x z) = μL.μ h ((f.f r).hom x) ((ρ.f s).hom z))

omit [CommRing k] in
theorem mappingCoconeNat_d_hom_apply' {k : Type u} [CommRing k]
    {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L) (n : ℕ) (x : K.X n)
    (y : shiftNegOneX L n) :
    ((mappingCoconeNat f).d n (n + 1)).hom ((x, y) : K.X n × shiftNegOneX L n) =
      (((K.d n (n + 1)).hom x, shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom y) :
        K.X (n + 1) × shiftNegOneX L (n + 1)) := by
  rw [mappingCoconeNat_d]
  rfl

/-- A cocone-left product of a cocycle `(x, y)` with a cocycle `e`, when `x · e = d q`, is the
connecting image of the cycle `y · e - f'(q)`. -/
theorem coconeLeft_homology_eq_homologyδ {p s m : ℕ} (h : p + 1 + s = m + 1)
    (X : (mappingCoconeNat f).cycles (p + 1)) (e : N.cycles s) (q : K'.X m) (w : L'.cycles m)
    (hq : (K'.d m (m + 1)).hom q =
      μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e))
    (hw : (L'.iCycles m).hom w =
      μL.μ (show p + s = m by omega)
        (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
        ((ρ.f s).hom ((N.iCycles s).hom e)) - (f'.f m).hom q) :
    (LeibnizPairing.coconeLeft μL ρ μK hc).homology h
        (((mappingCoconeNat f).homologyπ (p + 1)).hom X) ((N.homologyπ s).hom e) =
      (mappingCoconeNat.homologyδ f' m).hom ((L'.homologyπ m).hom w) := by
  rw [LeibnizPairing.homology_homologyπ]
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' m w
  rw [hc'1]
  have key : (LeibnizPairing.coconeLeft μL ρ μK hc).cycles h X e =
      c' + ((mappingCoconeNat f').toCycles m (m + 1)).hom
        ((q, 0) : K'.X m × shiftNegOneX L' m) := by
    apply iCycles_hom_injective
    have e1 := LeibnizPairing.iCycles_cycles (LeibnizPairing.coconeLeft μL ρ μK hc) h X e
    have e2 := iCycles_toCycles_hom_apply (mappingCoconeNat f') m (m + 1)
      ((q, 0) : K'.X m × shiftNegOneX L' m)
    rw [map_add, e1, e2, mappingCoconeNat_d_hom_apply']
    refine Prod.ext ?_ ?_
    · change μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e) =
        (((mappingCoconeNat f').iCycles (m + 1)).hom c').1 + (K'.d m (m + 1)).hom q
      rw [show (((mappingCoconeNat f').iCycles (m + 1)).hom c').1 = 0 from congrArg Prod.fst hc'2,
        zero_add, hq]
    · change μL.μ (show p + s = m by omega)
          (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
          ((ρ.f s).hom ((N.iCycles s).hom e)) =
        (((mappingCoconeNat f').iCycles (m + 1)).hom c').2 +
          (shiftNegOneSucc L' m ((f'.f m).hom q) + (shiftNegOneD L' m).hom 0)
      rw [show (((mappingCoconeNat f').iCycles (m + 1)).hom c').2 =
          shiftNegOneSucc L' m ((L'.iCycles m).hom w) from congrArg Prod.snd hc'2, map_zero, add_zero,
        shiftNegOneSucc_apply, shiftNegOneSucc_apply, hw]
      exact (sub_add_cancel _ _).symm
  rw [key, map_add]
  exact (congrArg (_ + ·) (homologyπ_toCycles_hom_apply (mappingCoconeNat f') m (m + 1)
    ((q, 0) : K'.X m × shiftNegOneX L' m))).trans (add_zero _)

/-- The existence form of `coconeLeft_homology_eq_homologyδ`. -/
theorem exists_coconeLeft_homology_eq_homologyδ {p s m : ℕ} (h : p + 1 + s = m + 1)
    (X : (mappingCoconeNat f).cycles (p + 1)) (e : N.cycles s) (q : K'.X m)
    (hq : (K'.d m (m + 1)).hom q =
      μK.μ h (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 ((N.iCycles s).hom e)) :
    ∃ w : L'.cycles m, (L'.iCycles m).hom w =
        μL.μ (show p + s = m by omega)
          (show L.X p from (((mappingCoconeNat f).iCycles (p + 1)).hom X).2)
          ((ρ.f s).hom ((N.iCycles s).hom e)) - (f'.f m).hom q ∧
      (LeibnizPairing.coconeLeft μL ρ μK hc).homology h
          (((mappingCoconeNat f).homologyπ (p + 1)).hom X) ((N.homologyπ s).hom e) =
        (mappingCoconeNat.homologyδ f' m).hom ((L'.homologyπ m).hom w) := by
  set x := (((mappingCoconeNat f).iCycles (p + 1)).hom X).1 with hx
  set y : L.X p := (((mappingCoconeNat f).iCycles (p + 1)).hom X).2 with hy
  have hX : ((mappingCoconeNat f).d (p + 1) (p + 1 + 1)).hom
      ((x, y) : K.X (p + 1) × shiftNegOneX L (p + 1)) = 0 :=
    iCycles_d_apply (mappingCoconeNat f) (p + 1) (p + 1 + 1) X
  rw [mappingCoconeNat_d_hom_apply' f (p + 1) x y] at hX
  have hdy : (L.d p (p + 1)).hom y = (f.f (p + 1)).hom x := by
    have h2 := congrArg Prod.snd hX
    rw [shiftNegOneD_succ_apply, shiftNegOneSucc_apply] at h2
    exact (add_neg_eq_zero.1 h2).symm
  have hd : (L'.d m (m + 1)).hom (μL.μ (show p + s = m by omega) y
      ((ρ.f s).hom ((N.iCycles s).hom e)) - (f'.f m).hom q) = 0 := by
    rw [map_sub, μL.leibniz, hdy, hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)),
      iCycles_d_apply, map_zero, map_zero, smul_zero, add_zero, ← hc h x,
      hom_apply_hom_apply_eq_of_comp_eq (f'.comm m (m + 1)), hq, sub_self]
  refine ⟨L'.cyclesMk _ (m + 1) (by simp) hd, L'.i_cyclesMk _ _ _ _, ?_⟩
  exact coconeLeft_homology_eq_homologyδ μL ρ μK hc h X e q _ hq (L'.i_cyclesMk _ _ _ _)

end Abstract

section Compact

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {A A' B C C' : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep A'] [IsSmoothRep B] [IsSmoothRep C]
  [IsSmoothRep C'] {Aᵥ A'ᵥ Cᵥ C'ᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)]
  [∀ v, IsSmoothRep (A'ᵥ v)] [∀ v, IsSmoothRep (Cᵥ v)] [∀ v, IsSmoothRep (C'ᵥ v)]
  {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v} {a' : ∀ v, Rep.res (φ v : H v →* G) A' ⟶ A'ᵥ v}
  {c : ∀ v, Rep.res (φ v : H v →* G) C ⟶ Cᵥ v} {c' : ∀ v, Rep.res (φ v : H v →* G) C' ⟶ C'ᵥ v}

omit [IsSmoothRep A] [∀ v, IsSmoothRep (Aᵥ v)] in
/-- The connecting map of the cocone on the class of a cycle of the local terms is `localToCompact`
of its components. -/
theorem homologyδ_homologyπ_eq_localToCompact {m : ℕ}
    (w : (piComplex fun v => cochains (Cᵥ v)).cycles m) :
    (mappingCoconeNat.homologyδ (localRes φ C Cᵥ c) m).hom
        (((piComplex fun v => cochains (Cᵥ v)).homologyπ m).hom w) =
      (GaloisCohomology.localToCompact φ C Cᵥ c m).hom (fun v => ((cochains (Cᵥ v)).homologyπ m).hom
        ((HomologicalComplex.cyclesMap (piProj (fun v => cochains (Cᵥ v)) v) m).hom w)) := by
  have e : (localCohomologyIso Cᵥ m).hom.hom
      (((piComplex fun v => cochains (Cᵥ v)).homologyπ m).hom w) =
      fun v => ((cochains (Cᵥ v)).homologyπ m).hom
        ((HomologicalComplex.cyclesMap (piProj (fun v => cochains (Cᵥ v)) v) m).hom w) :=
    funext fun v => (piHomologyIso_hom_apply _ m _ v).trans (homologyMap_homologyπ_apply _ m w)
  rw [← e, GaloisCohomology.localToCompact]
  exact (hom_apply_hom_apply_of_comp_eq (Iso.hom_inv_id_assoc (localCohomologyIso Cᵥ m) _) _).symm

/-- **Naturality of the cup product with compact support in the target.** -/
theorem compactSupportMap_compactCup (μ : A ⊗ B ⟶ C)
    (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
    (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v)
    (g : C ⟶ C') (gᵥ : ∀ v, Cᵥ v ⟶ C'ᵥ v)
    (hg : ∀ v, c v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ c' v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map (μ ≫ g) ≫ c' v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ (μᵥ v ≫ gᵥ v))
    {r s n : ℕ} (h : r + s = n) (x : compactSupportCohomology φ A Aᵥ a r) (y : cohomology B s) :
    (compactSupportMap φ g gᵥ hg n).hom (compactCup φ μ μᵥ hμ h x y) =
      compactCup φ (μ ≫ g) (fun v => μᵥ v ≫ gᵥ v) hμ' h x y := by
  refine LeibnizPairing.homologyMap_homology (compactCupLeibniz φ μ μᵥ hμ)
    (compactCupLeibniz φ (μ ≫ g) (fun v => μᵥ v ≫ gᵥ v) hμ') (compactSupportCochainsMap φ g gᵥ hg)
    ?_ h x y
  intro r s n h p z
  revert p
  intro (p : (cochains A).X r × shiftNegOneX (piComplex fun v => cochains (Aᵥ v)) r)
  obtain ⟨x0, b⟩ := p
  refine Prod.ext ?_ ?_
  · apply cochainOf_injective
    rfl
  · cases r with
    | zero =>
      cases n with
      | zero => rfl
      | succ m =>
        change ((piMap fun v => coeffCochainsMap (gᵥ v)).f m).hom 0 = 0
        exact map_zero _
    | succ r =>
      cases n with
      | zero => rfl
      | succ m =>
        revert b
        intro (b : (piComplex fun v => cochains (Aᵥ v)).X r)
        refine funext fun v => ?_
        apply cochainOf_injective
        rfl

/-- The cup product with compact support depends only on the local pairings, not on the proofs of
compatibility. -/
theorem compactCup_congr (μ : A ⊗ B ⟶ C) (μᵥ μᵥ' : ∀ v, Aᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Cᵥ v)
    (e : μᵥ = μᵥ') (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ v)
    (hμ' : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μ ≫ c v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μᵥ' v)
    {r s n : ℕ} (h : r + s = n) (x : compactSupportCohomology φ A Aᵥ a r) (y : cohomology B s) :
    compactCup φ μ μᵥ hμ h x y = compactCup φ μ μᵥ' hμ' h x y := by
  subst e
  rfl

end Compact

section ActionPairings

variable {K : Type u} [Group K]

theorem lsmul_uliftUp {A : Type u} [AddCommGroup A] [Module (ULift.{u} ℤ) A] (m : ℤ) (x : A) :
    (LinearMap.lsmul (ULift.{u} ℤ) A) (ULift.up m) x = m • x := by
  have h : (ULift.up m : ULift.{u} ℤ) = ((m : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  refine (LinearMap.lsmul_apply _ _).trans ?_
  rw [h]
  exact Int.cast_smul_eq_zsmul (ULift.{u} ℤ) m x

/-- The multiplication pairing `Res ℤ ⊗ A → A` for a module of a group `K` mapping to `G`. -/
def intMulPairingRes {G : Type u} [Group G] (A : Rep.{u} (ULift.{u} ℤ) K) (ψ : K →* G) :
    Rep.res ψ (intRepTriv G) ⊗ A ⟶ A :=
  pairingHom (LinearMap.lsmul (ULift.{u} ℤ) A) fun σ m a => ((A.ρ σ).map_smul m a).symm

/-- The action pairing `A ⊗ ℤ → A`, `a ⊗ m ↦ m • a`. -/
def intActPairing (A : Rep.{u} (ULift.{u} ℤ) K) : A ⊗ intRepTriv K ⟶ A :=
  (β_ A (intRepTriv K)).hom ≫ intMulPairing K A

theorem intActPairing_tmul (A : Rep.{u} (ULift.{u} ℤ) K) (a : A) (m : ℤ) :
    (intActPairing A).hom (a ⊗ₜ[ULift.{u} ℤ] (ULift.up m : intRepTriv K) :
      (A ⊗ intRepTriv K : Rep _ _)) = m • a :=
  intMulPairing_tmul K A m a

/-- The action pairing `A ⊗ Res ℤ → A` for a module of a group `K` mapping to `G`. -/
def intActPairingRes {G : Type u} [Group G] (A : Rep.{u} (ULift.{u} ℤ) K) (ψ : K →* G) :
    A ⊗ Rep.res ψ (intRepTriv G) ⟶ A :=
  (β_ A (Rep.res ψ (intRepTriv G))).hom ≫ intMulPairingRes A ψ

theorem intActPairingRes_tmul {G : Type u} [Group G] (A : Rep.{u} (ULift.{u} ℤ) K) (ψ : K →* G)
    (a : A) (m : ℤ) :
    (intActPairingRes A ψ).hom (a ⊗ₜ[ULift.{u} ℤ] (ULift.up m : Rep.res ψ (intRepTriv G)) :
      (A ⊗ Rep.res ψ (intRepTriv G) : Rep _ _)) = m • a :=
  (pairingHom_tmul (A := Rep.res ψ (intRepTriv G)) (B := A) (LinearMap.lsmul (ULift.{u} ℤ) A)
    (fun σ m a => ((A.ρ σ).map_smul m a).symm) (ULift.up m) a).trans (lsmul_uliftUp m a)

end ActionPairings

section GenericCompat

variable {G L : Type u} [Group G] [Group L] (n : ℕ)

theorem resTensorHom_id_id (ψ : L →* G) {A B : Rep.{u} (ULift.{u} ℤ) G} :
    resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) = 𝟙 _ :=
  Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl))

variable {D E : Rep.{u} (ULift.{u} ℤ) G} (hD : ∀ d : D, n • d = 0)

/-- `x ⊗ m ↦ m • f(x)` and `x ⊗ m ↦ f((m mod n) · x)` agree on a module killed by `n`. -/
theorem tensor_intActPairing_eq (f : D ⟶ E) :
    (f ⊗ₘ 𝟙 (intRepTriv G)) ≫ intActPairing E =
      (𝟙 D ⊗ₘ zmodReduction G n) ≫ (zmodMulPairingRight n D hD ≫ f) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun ζ m => ?_))
  obtain ⟨m⟩ := m
  change (intActPairing E).hom (f.hom ζ ⊗ₜ[ULift.{u} ℤ] (ULift.up m : intRepTriv G)) =
    f.hom ((zmodMulPairing n D hD).hom ((zmodReduction G n).hom (ULift.up m) ⊗ₜ[ULift.{u} ℤ] ζ))
  rw [intActPairing_tmul, zmodReduction_hom_apply, zmodMulPairing_tmul,
    zsmul_eq_zsmul_of_intCast_eq hD (ZMod.intCast_zmod_cast (m : ZMod n)) ζ, map_zsmul]

/-- The local form of `tensor_intActPairing_eq`. -/
theorem tensor_intActPairingRes_eq (ψ : L →* G) {Eᵥ : Rep.{u} (ULift.{u} ℤ) L}
    (f : Rep.res ψ D ⟶ Eᵥ) :
    (f ⊗ₘ 𝟙 (Rep.res ψ (intRepTriv G))) ≫ intActPairingRes Eᵥ ψ =
      (𝟙 (Rep.res ψ D) ⊗ₘ (Rep.resFunctor ψ).map (zmodReduction G n)) ≫
        ((Rep.resFunctor ψ).map (zmodMulPairingRight n D hD) ≫ f) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun ζ m => ?_))
  obtain ⟨m⟩ := m
  change (intActPairingRes Eᵥ ψ).hom (f.hom ζ ⊗ₜ[ULift.{u} ℤ] (ULift.up m : Rep.res ψ (intRepTriv G))) =
    f.hom ((zmodMulPairing n D hD).hom ((zmodReduction G n).hom (ULift.up m) ⊗ₜ[ULift.{u} ℤ] ζ))
  rw [intActPairingRes_tmul, zmodReduction_hom_apply, zmodMulPairing_tmul,
    zsmul_eq_zsmul_of_intCast_eq hD (ZMod.intCast_zmod_cast (m : ZMod n)) ζ, map_zsmul]

theorem tensor_nsmul_intActPairing_eq (A : Rep.{u} (ULift.{u} ℤ) G) :
    (𝟙 A ⊗ₘ (n • 𝟙 (intRepTriv G))) ≫ intActPairing A =
      ((n • 𝟙 A) ⊗ₘ 𝟙 (intRepTriv G)) ≫ intActPairing A := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun x m => ?_))
  obtain ⟨m⟩ := m
  change (intActPairing A).hom (x ⊗ₜ[ULift.{u} ℤ] (n • 𝟙 (intRepTriv G)).hom (ULift.up m)) =
    (intActPairing A).hom ((n • 𝟙 A).hom x ⊗ₜ[ULift.{u} ℤ] (ULift.up m : intRepTriv G))
  rw [nsmul_id_hom_apply, nsmul_id_hom_apply, intActPairing_tmul]
  have e : n • (ULift.up m : intRepTriv G) = ULift.up ((n : ℤ) * m) := by
    ext
    simp
  rw [e, intActPairing_tmul, mul_zsmul, natCast_zsmul, smul_comm]

theorem tensor_nsmul_intActPairingRes_eq (ψ : L →* G) (A : Rep.{u} (ULift.{u} ℤ) L) :
    (𝟙 A ⊗ₘ (Rep.resFunctor ψ).map (n • 𝟙 (intRepTriv G))) ≫ intActPairingRes A ψ =
      ((n • 𝟙 A) ⊗ₘ 𝟙 (Rep.res ψ (intRepTriv G))) ≫ intActPairingRes A ψ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun x m => ?_))
  obtain ⟨m⟩ := m
  change (intActPairingRes A ψ).hom (x ⊗ₜ[ULift.{u} ℤ] (n • 𝟙 (intRepTriv G)).hom (ULift.up m)) =
    (intActPairingRes A ψ).hom ((n • 𝟙 A).hom x ⊗ₜ[ULift.{u} ℤ]
      (ULift.up m : Rep.res ψ (intRepTriv G)))
  rw [nsmul_id_hom_apply, nsmul_id_hom_apply, intActPairingRes_tmul]
  have e : n • (ULift.up m : intRepTriv G) = ULift.up ((n : ℤ) * m) := by
    ext
    simp
  rw [e, intActPairingRes_tmul, mul_zsmul, natCast_zsmul, smul_comm]

/-- Restriction of a pairing composed with a map, against restricted local maps. -/
theorem res_comp_compat {Cᵥ : Rep.{u} (ULift.{u} ℤ) L} {X C' : Rep.{u} (ULift.{u} ℤ) G}
    (ψ : L →* G) (μ : D ⊗ E ⟶ X) (g : X ⟶ C') (c : Rep.res ψ C' ⟶ Cᵥ) (gᵥ : Rep.res ψ X ⟶ Cᵥ)
    (hg : 𝟙 (Rep.res ψ X) ≫ gᵥ = (Rep.resFunctor ψ).map g ≫ c) :
    (Rep.resFunctor ψ).map (μ ≫ g) ≫ c =
      resTensorHom ψ (𝟙 (Rep.res ψ D)) (𝟙 _) ≫ ((Rep.resFunctor ψ).map μ ≫ gᵥ) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun a b => ?_))
  exact (congrArg (fun F => F.hom (μ.hom (a ⊗ₜ[ULift.{u} ℤ] b))) hg).symm

theorem eq_of_add_neg_one_pow_one_smul_eq_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {a b : M} (h : a + (-1 : R) ^ 1 • b = 0) : a = b := by
  rw [pow_one, neg_smul, one_smul, add_neg_eq_zero] at h
  exact h

/-- Restriction of the action pairing against a local map. -/
theorem intActPairing_res_compat (ψ : L →* G) (A : Rep.{u} (ULift.{u} ℤ) G)
    {Aᵥ : Rep.{u} (ULift.{u} ℤ) L} (f : Rep.res ψ A ⟶ Aᵥ) :
    (Rep.resFunctor ψ).map (intActPairing A) ≫ f =
      resTensorHom ψ f (𝟙 _) ≫ intActPairingRes Aᵥ ψ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun a m => ?_))
  obtain ⟨m⟩ := m
  change f.hom ((intActPairing A).hom (a ⊗ₜ[ULift.{u} ℤ] (ULift.up m : intRepTriv G))) =
    (intActPairingRes Aᵥ ψ).hom (f.hom a ⊗ₜ[ULift.{u} ℤ] (ULift.up m : Rep.res ψ (intRepTriv G)))
  rw [intActPairing_tmul, intActPairingRes_tmul, map_zsmul]

end GenericCompat

section KummerCup

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))} (n : ℕ) [NeZero n]

variable (S) in
/-- The localization homomorphism at `v ∈ S`, as a monoid homomorphism. -/
abbrev localFamilyHom (v : S) :
    Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →*
      GaloisGroupUnramifiedOutside K Ω S :=
  (localFamily ι S v : Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →*
    GaloisGroupUnramifiedOutside K Ω S)

variable (S) in
/-- The cup product `H_c¹(G_S, 𝒪_Sˣ) × Hˢ(G_S, ℤ) → H_c^{1+s}(G_S, 𝒪_Sˣ)` along the action
`𝒪_Sˣ ⊗ ℤ → 𝒪_Sˣ` (and `K̄_vˣ ⊗ ℤ → K̄_vˣ` at the places of `S`). -/
def unitsCup (s : ℕ) :=
  compactCup (A := maximalSUnitsModule K Ω S) (B := intRepTriv (GaloisGroupUnramifiedOutside K Ω S))
    (C := maximalSUnitsModule K Ω S)
    (Aᵥ := fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (Cᵥ := fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (a := fun v => sUnitsLocalHom ι S v.1) (c := fun v => sUnitsLocalHom ι S v.1)
    (localFamily ι S) (intActPairing (maximalSUnitsModule K Ω S))
    (fun v => intActPairingRes (unitsModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K)))
      (localFamilyHom ι S v))
    (fun v => intActPairing_res_compat (localFamilyHom ι S v)
      (maximalSUnitsModule K Ω S) (sUnitsLocalHom ι S v.1)) (r := 1) (s := s) (n := 1 + s) rfl

/-- **Kummer and Bockstein.** The image in `H_c³(G_S, 𝒪_Sˣ)` of `δ_c(e) ∪ χ` (cup product
`μ_n ⊗ ℤ/n → μ_n`) is `e ∪ δχ` (cup product `𝒪_Sˣ ⊗ ℤ → 𝒪_Sˣ`). -/
theorem compactSupportMap_compactCupRes_kummerCompactδ
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (x : unitsCompact ι S 1) (y : cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :
    (compactSupportMap (localFamily ι S) (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n).f
      (fun v => (localKummerSequence ι S n v.1).f) (fun v => (kummerLocalMap ι S n v).comm₁₂) 3).hom
        (compactCupRes (localFamily ι S)
          (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
          (show 2 + 1 = 3 from rfl) ((kummerCompactδ ι n hS).hom x) y) =
      unitsCup ι S 2 x
        ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2 rfl).hom y) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hμ₁ : ∀ v : S, (Rep.resFunctor (localFamilyHom ι S v)).map
      (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n) ≫
        rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n) ≫ sUnitsLocalHom ι S v.1 =
      resTensorHom (A := dualizingModule K Ω S n)
        (B := zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) (localFamilyHom ι S v)
        (𝟙 (localModule ι (dualizingModule K Ω S n) v.1)) (𝟙 _) ≫
        ((Rep.resFunctor (localFamilyHom ι S v)).map
          (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n)) ≫
            rootsOfUnityLocalHom ι S n v.1) := fun v =>
    res_comp_compat (localFamilyHom ι S v)
      (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
      (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n)
      (sUnitsLocalHom ι S v.1) (rootsOfUnityLocalHom ι S n v.1) (kummerLocalMap ι S n v).comm₁₂
  have step1 := compactSupportMap_compactCup (localFamily ι S)
    (A := dualizingModule K Ω S n) (B := zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n)
    (C := dualizingModule K Ω S n) (C' := maximalSUnitsModule K Ω S)
    (Aᵥ := fun v : S => localModule ι (dualizingModule K Ω S n) v.1)
    (Cᵥ := fun v : S => localModule ι (dualizingModule K Ω S n) v.1)
    (C'ᵥ := fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (a := fun _ => 𝟙 _) (c := fun _ => 𝟙 _) (c' := fun v => sUnitsLocalHom ι S v.1)
    (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
    (fun v => (Rep.resFunctor (localFamilyHom ι S v)).map
      (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n)))
    (fun v => resFunctor_map_comp_id _ _)
    (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n)
    (fun v => rootsOfUnityLocalHom ι S n v.1) (fun v => (kummerLocalMap ι S n v).comm₁₂) hμ₁
    (show 2 + 1 = 3 from rfl) ((kummerCompactδ ι n hS).hom x) y
  refine step1.trans ?_
  have key := compactCup_compactSupportδ_add_compactCup_δ (localFamily ι S)
    (SA := sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n)
    (SAᵥ := fun v : S => localKummerSequence ι S n v.1) (kummerLocalMap ι S n)
    (SB := bockSeq (GaloisGroupUnramifiedOutside K Ω S) n) (C := maximalSUnitsModule K Ω S)
    (Cᵥ := fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (c := fun v => sUnitsLocalHom ι S v.1)
    (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n) ≫
      rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n)
    (intActPairing (maximalSUnitsModule K Ω S)) (intActPairing (maximalSUnitsModule K Ω S))
    (fun v => (Rep.resFunctor (localFamilyHom ι S v)).map
      (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n)) ≫
        rootsOfUnityLocalHom ι S n v.1)
    (fun v => intActPairingRes (unitsModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K))) (localFamilyHom ι S v))
    (fun v => intActPairingRes (unitsModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K))) (localFamilyHom ι S v))
    hμ₁
    (fun v => intActPairing_res_compat (localFamilyHom ι S v)
      (maximalSUnitsModule K Ω S) (sUnitsLocalHom ι S v.1))
    (fun v => intActPairing_res_compat (localFamilyHom ι S v)
      (maximalSUnitsModule K Ω S) (sUnitsLocalHom ι S v.1))
    (tensor_intActPairing_eq n (nsmul_dualizingModule S n)
      (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n))
    (tensor_nsmul_intActPairing_eq n (maximalSUnitsModule K Ω S))
    (fun v => tensor_intActPairingRes_eq n (nsmul_dualizingModule S n) (localFamilyHom ι S v)
      (rootsOfUnityLocalHom ι S n v.1))
    (fun v => tensor_nsmul_intActPairingRes_eq n (localFamilyHom ι S v)
      (unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))))
    (sUnitsKummerSequence_shortExact (Ω := Ω) S n (natCast_notMem_of_notMem n hS))
    (fun v => localKummerSequence_shortExact ι S n hS v.1)
    (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n))
    (r := 1) (s := 1) (n := 2) rfl rfl x y
  exact eq_of_add_neg_one_pow_one_smul_eq_zero key

end KummerCup


section Bockstein

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

/-- The Bockstein of a character `z ∈ H¹(G, ℤ/n)` is the class of the integer cocycle
`bockInt z`. -/
theorem exists_cocycle_δ_bockSeq (hn : n ≠ 0) (z : cocycles (zmodRep.{u} G n) 1) :
    ∃ x₁ : cocycles (intRepTriv G) 2,
      cohomologyπ _ 2 x₁ = (δ (bockSeq_shortExact G n hn) 1 2 rfl).hom (cohomologyπ _ 1 z) ∧
      ∀ g h : G, (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down = bockInt (zmodCocycleHom z) g h := by
  have : NeZero n := ⟨hn⟩
  have hS := bockSeq_shortExact G n hn
  have hχ : ∀ g h : G, zmodCocycleHom z (g * h) = zmodCocycleHom z g + zmodCocycleHom z h :=
    zmodCocycleHom_mul z
  have hlc : IsLocallyConstant fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G) :=
    IsLocallyConstant.comp ((isLocallyConstant_zmodCocycleHom z).comp_continuous (continuous_apply 0))
      (fun c : ZMod n => (ULift.up (c.val : ℤ) : ULift.{u} ℤ))
  let x₂ : (cochains (bockSeq G n).X₂).X 1 :=
    mkCochain (bockSeq G n).X₂ (fun v : Fin 1 → G =>
      (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ) : intRepTriv G)) hlc
  have hx₂ : (coeffCochainsMap (bockSeq G n).g).f 1 x₂ = cocycleι (bockSeq G n).X₃ 1 z := by
    apply cochainOf_injective
    rw [cochainOf_cochainsMap_f]
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    change (zmodReduction G n).hom (ULift.up ((zmodCocycleHom z (v 0)).val : ℤ)) =
      cochainOf _ (cocycleι _ 1 z) v
    rw [zmodReduction_hom_apply]
    apply ULift.ext
    change (((zmodCocycleHom z (v 0)).val : ℤ) : ZMod n) = (cochainOf _ (cocycleι _ 1 z) v).down
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    conv_rhs => rw [hv]
    rfl
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_map_f_eq_d hS 2 z x₂ hx₂
  have hδ := δ_cohomologyπ_of_lift hS rfl z x₂ hx₂ x₁ hx₁
  refine ⟨x₁, hδ.symm, fun g h => ?_⟩
  have e : cochainOf (bockSeq G n).X₂ ((coeffCochainsMap (bockSeq G n).f).f 2 (cocycleι _ 2 x₁)) ![g, h] =
      cochainOf (bockSeq G n).X₂ (((cochains (bockSeq G n).X₂).d 1 2).hom x₂) ![g, h] :=
    congrArg (fun c => cochainOf (bockSeq G n).X₂ c ![g, h]) hx₁
  rw [cochainOf_cochainsMap_f, cochainOf_d_one_apply] at e
  have e2 := congrArg ULift.down e
  change n • (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down =
    ((zmodCocycleHom z h).val : ℤ) - ((zmodCocycleHom z (g * h)).val : ℤ) +
      ((zmodCocycleHom z g).val : ℤ) at e2
  have e3 := natCast_mul_bockInt (zmodCocycleHom z) hχ g h
  rw [nsmul_eq_mul] at e2
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn)
  rw [e2, e3]
  ring

end Bockstein

section ConstCup

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cupCochain_const_left {A B : Rep.{u} k G} {q n : ℕ} (h : 0 + q = n) (m : A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    cupCochain h (fun _ => m) g x = m ⊗ₜ[k] g (fun j : Fin q => x ⟨j, by omega⟩) := by
  rw [cupCochain_apply]
  congr 1
  have h0 : Fin.partialProd x ⟨0, by omega⟩ = 1 := Fin.partialProd_zero x
  rw [h0, map_one, Module.End.one_apply]
  congr 1
  funext j
  congr 1
  ext
  simp

variable {U X B : Rep.{u} k G} [IsSmoothRep U] [IsSmoothRep X] [IsSmoothRep B] (j : U ⟶ X)
  (μU : U ⊗ B ⟶ U) (μX : X ⊗ B ⟶ X) (hj : μU ≫ j = (j ⊗ₘ 𝟙 B) ≫ μX)

/-- `m ∪ e - j(z)`, a cochain of `X`. -/
noncomputable def constCupSub (m : X) {s : ℕ} (e : (cochains B).X s) (z : (cochains U).X s) :
    (cochains X).X s :=
  cupPairingCochains μX (show 0 + s = s by omega) (zeroCochain X m) e - (coeffCochainsMap j).f s z

theorem cochainOf_constCupSub (m : X) {s : ℕ} (e : (cochains B).X s) (z : (cochains U).X s)
    (σ : Fin s → G) :
    cochainOf X (constCupSub j μX m e z) σ =
      μX.hom (m ⊗ₜ[k] cochainOf B e σ) - j.hom (cochainOf U z σ) := by
  change cochainOf X (cupPairingCochains μX (show 0 + s = s by omega) (zeroCochain X m) e) σ -
    cochainOf X ((coeffCochainsMap j).f s z) σ = _
  rw [cochainOf_cochainsMap_f, cochainOf_cupPairingCochains]
  congr 1
  refine (congrArg μX.hom (cupCochain_const_left (show 0 + s = s by omega) m _ σ)).trans ?_
  congr 3

include hj in
theorem d_constCupSub (m : X) (x : (cochains U).X 1)
    (hx : (coeffCochainsMap j).f 1 x = ((cochains X).d 0 1).hom (zeroCochain X m))
    {s : ℕ} (e : (cochains B).X s) (he : ((cochains B).d s (s + 1)).hom e = 0)
    (z : (cochains U).X s)
    (hz : ((cochains U).d s (s + 1)).hom z =
      cupPairingCochains μU (show 1 + s = s + 1 by omega) x e) :
    ((cochains X).d s (s + 1)).hom (constCupSub j μX m e z) = 0 := by
  have L := (cupLeibniz μX).leibniz (show 0 + s = s by omega) (zeroCochain X m) e
  change ((cochains X).d s (s + 1)).hom (cupPairingCochains μX _ (zeroCochain X m) e) = _ at L
  rw [constCupSub, map_sub, L, he, map_zero, smul_zero, add_zero, ← hx,
    hom_apply_hom_apply_eq_of_comp_eq ((coeffCochainsMap j).comm s (s + 1)) z, hz, sub_eq_zero]
  apply cochainOf_injective
  funext σ
  rw [cochainOf_cochainsMap_f]
  exact (cupCochain_tensorHom_eq' ((j ⊗ₘ 𝟙 B) ≫ μX) μX j rfl (show 1 + s = s + 1 by omega)
    (cochainOf U x) (cochainOf B e) σ).symm.trans (congrArg (fun f : U ⊗ B ⟶ X =>
      f.hom (cupCochain (show 1 + s = s + 1 by omega) (cochainOf U x) (cochainOf B e) σ)) hj.symm)

variable (Ωᵥ : ∀ v, Rep.{u} k (H v)) [∀ v, IsSmoothRep (Ωᵥ v)]
  (a : ∀ v, Rep.res (φ v : H v →* G) U ⟶ Ωᵥ v) (l : ∀ v, Rep.res (φ v : H v →* G) X ⟶ Ωᵥ v)
  (hal : ∀ v (x : U), (a v).hom x = (l v).hom (j.hom x))
  (μΩ : ∀ v, Ωᵥ v ⊗ Rep.res (φ v : H v →* G) B ⟶ Ωᵥ v)
  (hl : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μX ≫ l v =
    resTensorHom (φ v : H v →* G) (l v) (𝟙 _) ≫ μΩ v)

include hj hal hl in
/-- **The cup product of a class `(x, (l_v m)_v)` with `x = d m` in `X`.** If `x ∪ e = d z` with
`z` a cochain of `U`, then the cup product with compact support of the class with the class of
`e` is the image under `localToCompact` of the localizations of the cocycle `m ∪ e - j(z)` of
`X`. -/
theorem exists_compactCup_const
    (hμ : ∀ v, (Rep.resFunctor (φ v : H v →* G)).map μU ≫ a v =
      resTensorHom (φ v : H v →* G) (a v) (𝟙 _) ≫ μΩ v)
    (Xc : (compactSupportCochains φ U Ωᵥ a).cycles 1) (m : X) (x : (cochains U).X 1)
    (hX1 : (((compactSupportCochains φ U Ωᵥ a).iCycles 1).hom Xc).1 = x) (y : ∀ v, Ωᵥ v)
    (hX2 : (((compactSupportCochains φ U Ωᵥ a).iCycles 1).hom Xc).2 = piConst Ωᵥ y)
    (hy : ∀ v, y v = (l v).hom m)
    (hx : (coeffCochainsMap j).f 1 x = ((cochains X).d 0 1).hom (zeroCochain X m))
    {s : ℕ} (e : (cochains B).cycles s) (z : (cochains U).X s)
    (hz : ((cochains U).d s (s + 1)).hom z =
      cupPairingCochains μU (show 1 + s = s + 1 by omega) x (((cochains B).iCycles s).hom e)) :
    ∃ W : cocycles X s, cochainOf X (cocycleι X s W) =
        cochainOf X (constCupSub j μX m (((cochains B).iCycles s).hom e) z) ∧
      compactCup φ μU μΩ hμ (show 1 + s = s + 1 by omega)
          (((compactSupportCochains φ U Ωᵥ a).homologyπ 1).hom Xc)
          (((cochains B).homologyπ s).hom e) =
        (GaloisCohomology.localToCompact φ U Ωᵥ a s).hom
          (fun v => (map (φ v) (l v) s).hom (cohomologyπ X s W)) := by
  have hdW := d_constCupSub j μU μX hj m x hx (((cochains B).iCycles s).hom e)
    (iCycles_d_apply _ s (s + 1) e) z hz
  let W : cocycles X s := (cochains X).cyclesMk _ (s + 1) (by simp) hdW
  have hW : cochainOf X (cocycleι X s W) =
      cochainOf X (constCupSub j μX m (((cochains B).iCycles s).hom e) z) :=
    congrArg (cochainOf X) ((cochains X).i_cyclesMk _ _ _ _)
  refine ⟨W, hW, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := exists_coconeLeft_homology_eq_homologyδ
    (LeibnizPairing.pi fun v => cupLeibniz (μΩ v))
    (localRes φ B (fun v => Rep.res (φ v : H v →* G) B) fun _ => 𝟙 _) (cupLeibniz μU)
    (localRes_cupPairingCochains φ μU μΩ hμ) (show 0 + 1 + s = s + 1 by omega) Xc e z
    (hz.trans (congrArg (fun c => cupPairingCochains μU (show 1 + s = s + 1 by omega) c
      (((cochains B).iCycles s).hom e)) hX1.symm))
  refine hw2.trans ((homologyδ_homologyπ_eq_localToCompact φ w).trans (congrArg _ (funext fun v => ?_)))
  rw [map_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMap, hW]
  funext σ
  have e1 := iCycles_cyclesMap_apply (piProj (fun v => cochains (Ωᵥ v)) v) s w
  rw [cocycleι, e1, piProj_f_hom_apply, hw1, cochainOf_constCupSub, map_sub]
  change cochainOf (Ωᵥ v) (cupPairingCochains (μΩ v) (show 0 + s = s by omega)
      ((((compactSupportCochains φ U Ωᵥ a).iCycles 1).hom Xc).2 v)
      (((localRes φ B (fun v => Rep.res (φ v : H v →* G) B) fun _ => 𝟙 _).f s).hom
        (((cochains B).iCycles s).hom e) v)) σ -
    cochainOf (Ωᵥ v) (((localRes φ U Ωᵥ a).f s).hom z v) σ = _
  rw [hX2, piConst_apply, cochainOf_cupPairingCochains]
  congr 1
  · refine (congrArg (μΩ v).hom (cupCochain_const_left (show 0 + s = s by omega) (y v) _ σ)).trans ?_
    rw [hy v]
    exact (congrArg (fun f => f.hom ((m ⊗ₜ[k] cochainOf B (((cochains B).iCycles s).hom e)
      (⇑(φ v : H v →* G) ∘ σ)) : Rep.res (φ v : H v →* G) (X ⊗ B))) (hl v)).symm
  · exact hal v _

end ConstCup

section Exists

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]

/-- A cup product of cocycles whose class vanishes is the coboundary of a cochain. -/
theorem exists_d_eq_cupPairingCochains (μ : A ⊗ B ⟶ C) {p q m : ℕ} (h : p + q = m + 1)
    (x : cocycles A p) (y : cocycles B q)
    (h0 : cupPairing μ h (cohomologyπ A p x) (cohomologyπ B q y) = 0) :
    ∃ z : (cochains C).X m, ((cochains C).d m (m + 1)).hom z =
      cupPairingCochains μ h (cocycleι A p x) (cocycleι B q y) := by
  rw [cupPairing_cohomologyπ] at h0
  have h1 := (homologyπ_eq_zero_iff (cochains C) _).1 h0
  rw [CochainComplex.prev_nat_succ] at h1
  obtain ⟨z, hz⟩ := h1
  refine ⟨z, hz.trans (cochainOf_injective (funext fun σ => ?_))⟩
  refine (cochainOf_cocycleι_cyclesMap_cupCocycles μ h x y σ).trans ?_
  rw [cochainOf_cupPairingCochains]
  exact congrArg μ.hom (cupCochain_apply h _ _ σ).symm

end Exists

section UnitsCup

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n]

omit [IsSepClosure K Ω] [NeZero n] in
theorem intActPairing_sUnitsToUnits :
    intActPairing (maximalSUnitsModule K Ω S) ≫ sUnitsToUnits S (maximalUnramifiedOutside K Ω S) =
      (sUnitsToUnits S (maximalUnramifiedOutside K Ω S) ⊗ₘ
        𝟙 (intRepTriv (GaloisGroupUnramifiedOutside K Ω S))) ≫
        intActPairing (unitsModule K (maximalUnramifiedOutside K Ω S)) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (TensorProduct.ext' fun x m => ?_))
  obtain ⟨m⟩ := m
  change (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)).hom
      ((intActPairing (maximalSUnitsModule K Ω S)).hom
        (x ⊗ₜ[ULift.{u} ℤ] (ULift.up m : intRepTriv (GaloisGroupUnramifiedOutside K Ω S)))) =
    (intActPairing (unitsModule K (maximalUnramifiedOutside K Ω S))).hom
      ((sUnitsToUnits S (maximalUnramifiedOutside K Ω S)).hom x ⊗ₜ[ULift.{u} ℤ]
        (ULift.up m : intRepTriv (GaloisGroupUnramifiedOutside K Ω S)))
  rw [intActPairing_tmul, intActPairing_tmul, map_zsmul]

/-- An element `u` of `K_Sˣ` with `u = b • t - w` (additively) for an `S`-unit `w`. -/
theorem toMul_mul_zpow_inv_mem {M : Type*} [CommGroup M] (N : Subgroup M) (t : M) (b : ℤ) (w : M)
    (X : Additive M) (hX : X = b • Additive.ofMul t - Additive.ofMul w) (hw : w ∈ N) :
    Additive.toMul X * (t ^ b)⁻¹ ∈ N := by
  have e : Additive.toMul X * (t ^ b)⁻¹ = w⁻¹ := by
    rw [hX, toMul_sub, toMul_zsmul, toMul_ofMul, toMul_ofMul, div_eq_mul_inv, mul_comm (t ^ b) w⁻¹,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [e]
  exact N.inv_mem hw

/-- **The cup product of the class of `(t, 1)` with the Bockstein of `χ`.** It is the image under
`localToCompact` of the localizations of a `2`-cocycle `W` of `G_S` in `K_Sˣ` with
`W(g, h) ≡ t ^ {c_χ(g, h)}` modulo `𝒪_Sˣ`. -/
theorem exists_unitsData_cup_bock (hn : IsPrimePow n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (t : sInvariantSubgroup Ω S) (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :
    ∃ W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) :
          (maximalUnramifiedOutside K Ω S)ˣ) *
          ((t : (maximalUnramifiedOutside K Ω S)ˣ) ^ bockInt (zmodCocycleHom z) g h)⁻¹ ∈
            maximalSUnits K Ω S) ∧
      unitsCup ι S 2 (unitsData S ι (Additive.ofMul t, 0))
          ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2 rfl).hom
            (cohomologyπ _ 1 z)) =
        (GaloisCohomology.localToCompact (localFamily ι S) (maximalSUnitsModule K Ω S)
          (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
          (fun v => sUnitsLocalHom ι S v.1) 2).hom
          (fun v => (map (localFamily ι S v) (maximalUnitsLocalHom ι S v.1) 2).hom
            (cohomologyπ _ 2 W)) := by
  obtain ⟨ℓ, k, hℓ, hk, hnk⟩ := (isPrimePow_nat_iff n).1 hn
  have hℓS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv =>
    hS v (by
      rw [← hnk, Nat.cast_pow]
      exact v.asIdeal.pow_mem_of_mem hv k hk)
  obtain ⟨x₁, hx₁π, hx₁v⟩ := exists_cocycle_δ_bockSeq (NeZero.ne n) z
  let c : cocycles (maximalSUnitsModule K Ω S) 1 :=
    (cochains (maximalSUnitsModule K Ω S)).cyclesMk (sInvCochain Ω S t) 2 (by simp)
      (d_sInvCochain Ω S t)
  have hc : cocycleι _ 1 c = sInvCochain Ω S t := (cochains (maximalSUnitsModule K Ω S)).i_cyclesMk _ _ _ _
  have hnz : n • cohomologyπ (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1 z = 0 :=
    nsmul_cohomology_eq_zero _ (nsmul_zmodRep_eq_zero _ n) 1 _
  have hb' : n • cohomologyπ _ 2 x₁ = 0 := by
    rw [hx₁π, ← map_nsmul, hnz, map_zero]
  have h0 : cupPairing (intActPairing (maximalSUnitsModule K Ω S)) (show 1 + 2 = 2 + 1 from rfl)
      (cohomologyπ _ 1 c) (cohomologyπ _ 2 x₁) = 0 := by
    refine eq_zero_of_cohomology_three_maximalSUnits S hℓ hℓS _ (k := k) ?_
    rw [hnk, ← map_nsmul, hb', map_zero]
  obtain ⟨z', hz'⟩ := exists_d_eq_cupPairingCochains (intActPairing (maximalSUnitsModule K Ω S))
    (show 1 + 2 = 2 + 1 from rfl) c x₁ h0
  have hz'' := hz'.trans (congrArg (fun a => cupPairingCochains (intActPairing (maximalSUnitsModule K Ω S))
    (show 1 + 2 = 2 + 1 from rfl) a (cocycleι _ 2 x₁)) hc)
  let d : UnitsDatum Ω S := (Additive.ofMul t, 0)
  have hX := iCycles_dataCycle (localFamily ι S)
    (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (fun v => sUnitsLocalHom ι S v.1) (sInvCochainHom Ω S d) (dataLocalHom S ι d)
    (d_sInvCochain Ω S _) (dataCond_unitsDatum S ι d)
  have key := exists_compactCup_const (localFamily ι S) (sUnitsToUnits S (maximalUnramifiedOutside K Ω S))
    (intActPairing (maximalSUnitsModule K Ω S)) (intActPairing (unitsModule K (maximalUnramifiedOutside K Ω S)))
    (intActPairing_sUnitsToUnits S)
    (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
    (fun v => sUnitsLocalHom ι S v.1) (fun v => maximalUnitsLocalHom ι S v.1) (fun _ _ => rfl)
    (fun v => intActPairingRes (unitsModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K))) (localFamilyHom ι S v))
    (fun v => intActPairing_res_compat (localFamilyHom ι S v)
      (unitsModule K (maximalUnramifiedOutside K Ω S)) (maximalUnitsLocalHom ι S v.1))
    (fun v => intActPairing_res_compat (localFamilyHom ι S v)
      (maximalSUnitsModule K Ω S) (sUnitsLocalHom ι S v.1))
    (dataCycle (localFamily ι S)
      (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
      (fun v => sUnitsLocalHom ι S v.1) (sInvCochainHom Ω S d) (dataLocalHom S ι d)
      (d_sInvCochain Ω S _) (dataCond_unitsDatum S ι d))
    (Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ)) (sInvCochain Ω S t)
    (congrArg Prod.fst hX) _ (congrArg Prod.snd hX)
    (fun v => (congrArg (· + sInvLocalHom S ι v.1 (Additive.ofMul t)) (map_zero (localUnitsHom v.1))).trans
      (zero_add _))
    (cochainsMap_sUnitsToUnits_sInvCochain Ω S t) x₁ z' hz''
  obtain ⟨W, hW, hcup⟩ := key
  refine ⟨W, fun g h => ?_, ?_⟩
  · have e1 := (congrFun hW ![g, h]).trans (cochainOf_constCupSub _ _ _ _ _ _)
    have e2 := intActPairing_tmul (unitsModule K (maximalUnramifiedOutside K Ω S))
      (Additive.ofMul (t : (maximalUnramifiedOutside K Ω S)ˣ))
      (cochainOf _ (cocycleι _ 2 x₁) ![g, h]).down
    refine toMul_mul_zpow_inv_mem (maximalSUnits K Ω S) _ _
      ((Additive.toMul (cochainOf _ z' ![g, h]) : maximalSUnits K Ω S) : (maximalUnramifiedOutside K Ω S)ˣ)
      _ ?_ (Additive.toMul (cochainOf _ z' ![g, h])).2
    refine e1.trans ?_
    rw [← hx₁v g h]
    exact congrArg₂ (· - ·) e2 rfl
  · rw [← hx₁π]
    exact hcup

/-- The local cup symbol `a_v ∪ δχ_v ∈ H²(K_v, K̄_vˣ)` of a unit `a_v ∈ K_vˣ` with the localization of
a class `b ∈ H²(G_S, ℤ)`. -/
def localUnitsCup (v : S) (a : Additive (v.1.adicCompletion K)ˣ)
    (b : cohomology (intRepTriv (GaloisGroupUnramifiedOutside K Ω S)) 2) :
    cohomology (unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K))) 2 :=
  haveI : IsSmoothRep (Rep.res (localFamilyHom ι S v) (intRepTriv (GaloisGroupUnramifiedOutside K Ω S))) :=
    isSmoothRep_res (localFamily ι S v) _
  cupPairing (intActPairingRes (unitsModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K))) (localFamilyHom ι S v)) (show 0 + 2 = 2 from rfl)
    ((zeroIso _).inv.hom (unitsToInvariants _ _ a)) ((map (localFamily ι S v) (𝟙 _) 2).hom b)

/-- **The cup product of the class of a datum `(t, a)` with the Bockstein of `χ`**: the image under
`localToCompact` of `(W|_{K_v} + a_v ∪ δχ_v)_v`, `W` a `2`-cocycle of `G_S` in `K_Sˣ` with
`W ≡ t ^ {c_χ}` modulo `𝒪_Sˣ`. -/
theorem exists_unitsData_cup_bock' (hn : IsPrimePow n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (d : UnitsDatum Ω S) (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :
    ∃ W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) :
          (maximalUnramifiedOutside K Ω S)ˣ) *
          (((Additive.toMul d.1 : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) ^
            bockInt (zmodCocycleHom z) g h)⁻¹ ∈ maximalSUnits K Ω S) ∧
      unitsCup ι S 2 (unitsData S ι d)
          ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2 rfl).hom
            (cohomologyπ _ 1 z)) =
        (GaloisCohomology.localToCompact (localFamily ι S) (maximalSUnitsModule K Ω S)
          (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
          (fun v => sUnitsLocalHom ι S v.1) 2).hom
          (fun v => (map (localFamily ι S v) (maximalUnitsLocalHom ι S v.1) 2).hom
              (cohomologyπ _ 2 W) +
            localUnitsCup ι S v (d.2 v)
              ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2
                rfl).hom (cohomologyπ _ 1 z))) := by
  obtain ⟨W, hW, hcup⟩ := exists_unitsData_cup_bock ι S n hn hS (Additive.toMul d.1) z
  refine ⟨W, hW, ?_⟩
  have hd : unitsData S ι d = unitsData S ι (Additive.ofMul (Additive.toMul d.1), 0) +
      unitsData S ι (0, d.2) :=
    (congrArg (unitsData S ι) (Prod.ext (add_zero _).symm (zero_add _).symm)).trans (map_add _ _ _)
  have eloc := compactCup_localToCompact (localFamily ι S) (intActPairing (maximalSUnitsModule K Ω S))
    (fun v => intActPairingRes (unitsModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K))) (localFamilyHom ι S v))
    (fun v => intActPairing_res_compat (localFamilyHom ι S v)
      (maximalSUnitsModule K Ω S) (sUnitsLocalHom ι S v.1))
    (show 0 + 2 = 2 from rfl) (show 0 + 1 + 2 = 2 + 1 from rfl)
    (fun v => (zeroIso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2 rfl).hom
      (cohomologyπ _ 1 z))
  rw [hd, map_add, LinearMap.add_apply, hcup, unitsData_zero_left]
  refine (congrArg (_ + ·) eloc).trans ?_
  rw [← map_add]
  rfl

end UnitsCup

section Formula

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n]

/-- **The cup product of the Kummer class with compact support of a datum with a character**, in
`H_c³(G_S, 𝒪_Sˣ)`. -/
theorem exists_compactCupRes_kummerCompactδ_unitsData (hn : IsPrimePow n)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (d : UnitsDatum Ω S) (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :
    ∃ W : cocycles (unitsModule K (maximalUnramifiedOutside K Ω S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) :
          (maximalUnramifiedOutside K Ω S)ˣ) *
          (((Additive.toMul d.1 : sInvariantSubgroup Ω S) : (maximalUnramifiedOutside K Ω S)ˣ) ^
            bockInt (zmodCocycleHom z) g h)⁻¹ ∈ maximalSUnits K Ω S) ∧
      (compactSupportMap (localFamily ι S) (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) n).f
        (fun v => (localKummerSequence ι S n v.1).f) (fun v => (kummerLocalMap ι S n v).comm₁₂) 3).hom
          (compactCupRes (localFamily ι S)
            (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
            (show 2 + 1 = 3 from rfl) ((kummerCompactδ ι n hS).hom (unitsData S ι d))
            (cohomologyπ _ 1 z)) =
        (GaloisCohomology.localToCompact (localFamily ι S) (maximalSUnitsModule K Ω S)
          (fun v : S => unitsModule (v.1.adicCompletion K) (AlgebraicClosure (v.1.adicCompletion K)))
          (fun v => sUnitsLocalHom ι S v.1) 2).hom
          (fun v => (map (localFamily ι S v) (maximalUnitsLocalHom ι S v.1) 2).hom
              (cohomologyπ _ 2 W) +
            localUnitsCup ι S v (d.2 v)
              ((δ (bockSeq_shortExact (GaloisGroupUnramifiedOutside K Ω S) n (NeZero.ne n)) 1 2
                rfl).hom (cohomologyπ _ 1 z))) := by
  obtain ⟨W, hW, hcup⟩ := exists_unitsData_cup_bock' ι S n hn hS d z
  exact ⟨W, hW, (compactSupportMap_compactCupRes_kummerCompactδ ι n hS _ _).trans hcup⟩

end Formula

end

end Langlands.GaloisCohomology.PoitouTate.Internal
