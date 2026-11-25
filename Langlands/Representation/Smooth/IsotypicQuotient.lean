import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Maximal isotypic quotients and the big theta lift of a representation of `G × H`

GKT §13.2.2 (pp. 391–393: (13.1), Lemma 13.4, (13.2), Lemma 13.6, Proposition 13.7,
Corollary 13.8), for any representation `ω` of a product of groups `G × H`, independent of where
`ω` comes from.

* `isotypicKernel ω π`: the intersection `S(π)` of the kernels of the `G`-intertwining maps
  `S → π` ((13.1)); it is stable under `G × H` (`isotypicKernel_stable`, Lemma 13.4).
* `BigThetaSpace ω π = (S ⊗ π^∨)_G`, the coinvariants of `G` acting on `S ⊗ π^∨` with `π^∨` the
  smooth contragredient, and `bigTheta ω π`, the representation of `H` on it ((13.2)).

For `G` with a cofinal family of compact open subgroups, `π` admissible and `ω` smooth on `G`:

* `homEquivThetaDual`: `Hom_G(ω, π) ≅ Θ_ω(π)^*` (Lemma 13.6, (13.4));
  `nontrivial_bigThetaSpace_iff`: `Θ_ω(π) ≠ 0` iff `π` is a quotient of `ω|_G` (Proposition 13.18).
* `homEquivThetaHom`: `Hom_{G×H}(ω, π ⊠ σ) ≅ Hom_H(Θ_ω(π), σ)` for every `σ` (Corollary 13.8).
* `isotypicQuotientMap : ω → π ⊠ Θ_ω(π)`, with kernel `S(π)` (`ker_isotypicQuotientMap`), onto for
  irreducible `π` (`isotypicQuotientMap_surjective`), and `isotypicQuotientEquiv :
  S / S(π) ≅ π ⊗ Θ_ω(π)` (Proposition 13.7). On the way: Schur's lemma for admissible irreducible
  representations (`exists_eq_smul_of_isAdmissible`) and the density theorem
  (`exists_asAlgebraHom_eq`, from Mathlib's `jacobson_density`).
-/

noncomputable section

open TensorProduct

namespace Langlands

universe uG uH uS uV uW

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  {S : Type uS} [AddCommGroup S] [Module ℂ S] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

section Kernel

variable (ω : Representation ℂ (G × H) S) (π : Representation ℂ G V)

/-- The restriction of a representation of `G × H` to `G`. -/
abbrev restrictLeft : Representation ℂ G S := ω.comp (MonoidHom.inl G H)

/-- The restriction of a representation of `G × H` to `H`. -/
abbrev restrictRight : Representation ℂ H S := ω.comp (MonoidHom.inr G H)

/-- The `G` and `H` actions commute: `ω(g, 1) ω(1, h) = ω(1, h) ω(g, 1)`. -/
theorem inl_mul_inr_comm (g : G) (h : H) :
    ω (MonoidHom.inl G H g) * ω (MonoidHom.inr G H h) =
      ω (MonoidHom.inr G H h) * ω (MonoidHom.inl G H g) := by
  rw [← map_mul, ← map_mul]
  congr 1
  ext <;> simp

/-- **The kernel `S(π)`** (GKT (13.1), p. 391): the intersection of the kernels of the
`G`-intertwining maps from `S` to `π`. The quotient `S / S(π)` is the maximal `π`-isotypic
quotient (GKT Proposition 13.5). -/
def isotypicKernel : Submodule ℂ S :=
  ⨅ f : (restrictLeft ω).IntertwiningMap π, LinearMap.ker f.toLinearMap

theorem mem_isotypicKernel {s : S} :
    s ∈ isotypicKernel ω π ↔ ∀ f : (restrictLeft ω).IntertwiningMap π, f s = 0 := by
  simp only [isotypicKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

/-- The `G`-intertwining map `s ↦ f(ω(1, h) s)` (the proof of GKT Lemma 13.4). -/
def intertwiningCompInr
    (f : (restrictLeft ω).IntertwiningMap π) (h : H) :
    (restrictLeft ω).IntertwiningMap π where
  toLinearMap := f.toLinearMap ∘ₗ ω (MonoidHom.inr G H h)
  isIntertwining' g := by
    rw [LinearMap.comp_assoc, MonoidHom.comp_apply, ← Module.End.mul_eq_comp,
      ← inl_mul_inr_comm, Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
      ← MonoidHom.comp_apply ω (MonoidHom.inl G H), f.isIntertwining', LinearMap.comp_assoc]

/-- **`S(π)` is stable under `G × H`** (GKT Lemma 13.4, p. 391). -/
theorem isotypicKernel_stable (p : G × H) {s : S} (hs : s ∈ isotypicKernel ω π) :
    ω p s ∈ isotypicKernel ω π := by
  rw [mem_isotypicKernel] at hs ⊢
  intro f
  have hp : p = MonoidHom.inl G H p.1 * MonoidHom.inr G H p.2 := by ext <;> simp
  rw [hp, map_mul, Module.End.mul_apply]
  have := Representation.IntertwiningMap.isIntertwining (restrictLeft ω) π f p.1
    (ω (MonoidHom.inr G H p.2) s)
  refine this.trans ?_
  rw [show f (ω (MonoidHom.inr G H p.2) s) = 0 from hs (intertwiningCompInr ω π f p.2), map_zero]

/-- `S(π)` as a subrepresentation of `ω`. -/
def isotypicKernelSubrep : Subrepresentation ω where
  toSubmodule := isotypicKernel ω π
  apply_mem_toSubmodule p _ hs := isotypicKernel_stable ω π p hs

variable (σ : Representation ℂ H W)

/-- The external tensor product `π ⊠ σ`, a representation of `G × H` on `V ⊗ W`. -/
abbrev outerTensor : Representation ℂ (G × H) (V ⊗[ℂ] W) :=
  Representation.tprod (π.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

end Kernel

section Contract

/-- `λ ⊗ 1 : V ⊗ W → W` for a linear form `λ` on `V`. -/
def contractLeft (l : Module.Dual ℂ V) : V ⊗[ℂ] W →ₗ[ℂ] W :=
  (TensorProduct.lid ℂ W).toLinearMap ∘ₗ l.rTensor W

theorem contractLeft_tmul (l : Module.Dual ℂ V) (v : V) (w : W) :
    contractLeft l (v ⊗ₜ w) = l v • w := by
  simp [contractLeft]

theorem contractLeft_add (l l' : Module.Dual ℂ V) (x : V ⊗[ℂ] W) :
    contractLeft (l + l') x = contractLeft l x + contractLeft l' x := by
  simp [contractLeft, LinearMap.rTensor_add]

theorem contractLeft_smul (c : ℂ) (l : Module.Dual ℂ V) (x : V ⊗[ℂ] W) :
    contractLeft (c • l) x = c • contractLeft l x := by
  simp [contractLeft, LinearMap.rTensor_smul]

theorem contractLeft_map (l : Module.Dual ℂ V) {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (T : V' →ₗ[ℂ] V) (x : V' ⊗[ℂ] W) :
    contractLeft l (TensorProduct.map T LinearMap.id x) = contractLeft (l ∘ₗ T) x := by
  induction x using TensorProduct.inductionOn with
  | tmul v w => simp [contractLeft_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem contractLeft_map_right (l : Module.Dual ℂ V) {W' : Type*} [AddCommGroup W']
    [Module ℂ W'] (T : W →ₗ[ℂ] W') (x : V ⊗[ℂ] W) :
    contractLeft l (TensorProduct.map LinearMap.id T x) = T (contractLeft l x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w => simp [contractLeft_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Contract

section Theta

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (ω : Representation ℂ (G × H) S) (π : Representation ℂ G V)

/-- The representation `ω|_G ⊗ π^∨` of `G` on `S ⊗ π^∨`, with `π^∨` the smooth contragredient. -/
abbrev thetaTensor : Representation ℂ G (S ⊗[ℂ] SmoothDual π) :=
  Representation.tprod (restrictLeft ω) (smoothContragredient π)

/-- **The space of the big theta lift** `Θ_ω(π) = (S ⊗ π^∨)_G` (GKT (13.2), p. 391; (13.8),
p. 400): the coinvariants of `G` on `S ⊗ π^∨`. -/
abbrev BigThetaSpace := (thetaTensor ω π).Coinvariants

/-- `ω(1, h) ⊗ 1`, a `G`-intertwiner of `ω|_G ⊗ π^∨`. -/
def thetaTensorRight (h : H) : (thetaTensor ω π).IntertwiningMap (thetaTensor ω π) where
  toLinearMap := TensorProduct.map (ω (MonoidHom.inr G H h)) LinearMap.id
  isIntertwining' g := by
    change TensorProduct.map (ω (MonoidHom.inr G H h)) LinearMap.id ∘ₗ
        TensorProduct.map (ω (MonoidHom.inl G H g)) (smoothContragredient π g) =
      TensorProduct.map (ω (MonoidHom.inl G H g)) (smoothContragredient π g) ∘ₗ
        TensorProduct.map (ω (MonoidHom.inr G H h)) LinearMap.id
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
      ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, inl_mul_inr_comm]

/-- **The big theta lift** `Θ_ω(π)` (GKT (13.2), Definition 13.17): the representation of `H` on
`(S ⊗ π^∨)_G` induced by `ω(1, h) ⊗ 1`. -/
def bigTheta : Representation ℂ H (BigThetaSpace ω π) where
  toFun h := Representation.Coinvariants.map _ _ (thetaTensorRight ω π h)
  map_one' := by
    have e : thetaTensorRight ω π 1 = Representation.IntertwiningMap.id _ := by
      refine Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_)
      change TensorProduct.map (ω (MonoidHom.inr G H 1)) LinearMap.id x = x
      rw [map_one, map_one, Module.End.one_eq_id, TensorProduct.map_id]
      rfl
    rw [e, Representation.Coinvariants.map_id]
    rfl
  map_mul' h h' := by
    rw [Module.End.mul_eq_comp, Representation.Coinvariants.map_comp]
    congr 1
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_)
    change TensorProduct.map (ω (MonoidHom.inr G H (h * h'))) LinearMap.id x =
      TensorProduct.map (ω (MonoidHom.inr G H h)) LinearMap.id
        (TensorProduct.map (ω (MonoidHom.inr G H h')) LinearMap.id x)
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, map_mul, map_mul, LinearMap.id_comp]
    rfl

theorem bigTheta_mk (h : H) (s : S) (l : SmoothDual π) :
    bigTheta ω π h (Representation.Coinvariants.mk _ (s ⊗ₜ l)) =
      Representation.Coinvariants.mk _ (ω (MonoidHom.inr G H h) s ⊗ₜ l) := rfl

/-- `[g s ⊗ λ] = [s ⊗ g⁻¹ λ]` in the coinvariants. -/
theorem mk_tmul_inl (g : G) (s : S) (l : SmoothDual π) :
    Representation.Coinvariants.mk (thetaTensor ω π) (ω (MonoidHom.inl G H g) s ⊗ₜ l) =
      Representation.Coinvariants.mk (thetaTensor ω π) (s ⊗ₜ[ℂ] smoothContragredient π g⁻¹ l) := by
  rw [← Representation.Coinvariants.mk_self_apply (thetaTensor ω π) g
    (s ⊗ₜ[ℂ] smoothContragredient π g⁻¹ l)]
  congr 1
  change ω (MonoidHom.inl G H g) s ⊗ₜ[ℂ] l = ω (MonoidHom.inl G H g) s ⊗ₜ[ℂ]
    (smoothContragredient π g (smoothContragredient π g⁻¹ l))
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-! ### `Θ_ω(π)^* = Hom_G(ω, π)` (GKT Lemma 13.6) -/

/-- The value of the smooth contragredient: `(g λ)(v) = λ(g⁻¹ v)`. -/
theorem smoothContragredient_apply_apply (g : G) (l : SmoothDual π) (v : V) :
    (smoothContragredient π g l).val v = l.val (π g⁻¹ v) := rfl

/-- The linear form `s ⊗ λ ↦ λ(f s)` of a `G`-intertwiner `f : ω → π`. -/
def homPairing (f : (restrictLeft ω).IntertwiningMap π) : S ⊗[ℂ] SmoothDual π →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((smoothDualPairing π).flip ∘ₗ f.toLinearMap)

omit [IsTopologicalGroup G] in
theorem homPairing_tmul (f : (restrictLeft ω).IntertwiningMap π) (s : S) (l : SmoothDual π) :
    homPairing ω π f (s ⊗ₜ l) = l.val (f s) := rfl

theorem homPairing_comp (f : (restrictLeft ω).IntertwiningMap π) (g : G) :
    homPairing ω π f ∘ₗ thetaTensor ω π g = homPairing ω π f := by
  refine TensorProduct.ext' fun s l => ?_
  change (smoothContragredient π g l).val (f (restrictLeft ω g s)) = l.val (f s)
  rw [smoothContragredient_apply_apply, Representation.IntertwiningMap.isIntertwining,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- `f ↦ (s ⊗ λ ↦ λ(f s))`, from `Hom_G(ω, π)` to the dual of `Θ_ω(π)` (GKT (13.4)). -/
def homToThetaDual :
    (restrictLeft ω).IntertwiningMap π →ₗ[ℂ] Module.Dual ℂ (BigThetaSpace ω π) where
  toFun f := Representation.Coinvariants.lift _ (homPairing ω π f) (homPairing_comp ω π f)
  map_add' f f' := Representation.Coinvariants.hom_ext <| TensorProduct.ext' fun s l => by
    change l.val (f s + f' s) = l.val (f s) + l.val (f' s)
    exact map_add _ _ _
  map_smul' c f := Representation.Coinvariants.hom_ext <| TensorProduct.ext' fun s l => by
    change l.val (c • f s) = c • l.val (f s)
    exact map_smul _ _ _

theorem homToThetaDual_mk (f : (restrictLeft ω).IntertwiningMap π) (s : S) (l : SmoothDual π) :
    homToThetaDual ω π f (Representation.Coinvariants.mk _ (s ⊗ₜ l)) = l.val (f s) := rfl

section Duality

variable {ω π}

/-- The value of the smooth bidual: `(ev v)(λ) = λ(v)`. -/
theorem smoothBidual_apply_apply (hπ : IsSmooth π) (v : V) (l : SmoothDual π) :
    (smoothBidual hπ v).val l = l.val v := rfl

variable (hω : IsSmooth (restrictLeft ω)) (hπ : IsAdmissible π)
  (hG : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

variable (π) in
/-- The smooth bidual of an admissible representation of a group with a cofinal family of compact
open subgroups, as a linear equivalence `π ≅ π^∨∨`. -/
def admissibleBidualEquiv : V ≃ₗ[ℂ] SmoothDual (smoothContragredient π) :=
  LinearEquiv.ofBijective (smoothBidual hπ.1).toLinearMap
    ⟨smoothBidual_injective_of_compact_cofinal hG π hπ.1,
      smoothBidual_surjective_of_compact_cofinal hG π hπ⟩

theorem admissibleBidualEquiv_apply (v : V) :
    admissibleBidualEquiv π hπ hG v = smoothBidual hπ.1 v := rfl

theorem admissibleBidualEquiv_map (g : G) (v : V) :
    admissibleBidualEquiv π hπ hG (π g v) =
      smoothContragredient (smoothContragredient π) g (admissibleBidualEquiv π hπ hG v) :=
  Representation.IntertwiningMap.isIntertwining _ _ (smoothBidual hπ.1) g v

variable (ω π) in
/-- For `ℓ ∈ Θ_ω(π)^*` and `s ∈ S`, the smooth functional `λ ↦ ℓ[s ⊗ λ]` on `π^∨`. -/
def thetaFunctional (ℓ : Module.Dual ℂ (BigThetaSpace ω π)) :
    S →ₗ[ℂ] SmoothDual (smoothContragredient π) :=
  LinearMap.codRestrict (smoothVectors (smoothContragredient π).dual)
    ((TensorProduct.mk ℂ S (SmoothDual π)).compr₂ (ℓ ∘ₗ Representation.Coinvariants.mk _))
    (fun s => by
      obtain ⟨K, hK⟩ := hω s
      refine ⟨K, fun k => LinearMap.ext fun l => ?_⟩
      change ℓ (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] smoothContragredient π (k : G)⁻¹ l)) =
        ℓ (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l))
      rw [← mk_tmul_inl]
      congr 3
      exact hK k)

theorem thetaFunctional_apply (ℓ : Module.Dual ℂ (BigThetaSpace ω π)) (s : S)
    (l : SmoothDual π) :
    (thetaFunctional ω π hω ℓ s).val l = ℓ (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l)) := rfl

theorem thetaFunctional_map (ℓ : Module.Dual ℂ (BigThetaSpace ω π)) (g : G) (s : S) :
    thetaFunctional ω π hω ℓ (ω (MonoidHom.inl G H g) s) =
      smoothContragredient (smoothContragredient π) g (thetaFunctional ω π hω ℓ s) :=
  Subtype.ext <| LinearMap.ext fun l => by
    change ℓ (Representation.Coinvariants.mk _ (ω (MonoidHom.inl G H g) s ⊗ₜ[ℂ] l)) =
      ℓ (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] smoothContragredient π g⁻¹ l))
    rw [mk_tmul_inl]

variable (ω π) in
/-- `ℓ ↦ (s ↦ the vector v with λ(v) = ℓ[s ⊗ λ])`, from the dual of `Θ_ω(π)` to `Hom_G(ω, π)`. -/
def thetaDualToHom (ℓ : Module.Dual ℂ (BigThetaSpace ω π)) :
    (restrictLeft ω).IntertwiningMap π where
  toLinearMap := (admissibleBidualEquiv π hπ hG).symm.toLinearMap ∘ₗ thetaFunctional ω π hω ℓ
  isIntertwining' g := LinearMap.ext fun s => by
    change (admissibleBidualEquiv π hπ hG).symm (thetaFunctional ω π hω ℓ
      (ω (MonoidHom.inl G H g) s)) =
        π g ((admissibleBidualEquiv π hπ hG).symm (thetaFunctional ω π hω ℓ s))
    rw [LinearEquiv.symm_apply_eq, admissibleBidualEquiv_map, LinearEquiv.apply_symm_apply,
      thetaFunctional_map]

/-- **`Θ_ω(π)^* = Hom_G(ω, π)`** (GKT (13.4) and Lemma 13.6, p. 392; Proposition 13.18, p. 400):
for an admissible `π` of a group with a cofinal family of compact open subgroups and `ω` smooth
on `G`, `f ↦ (s ⊗ λ ↦ λ(f s))` is a linear equivalence. -/
def homEquivThetaDual :
    (restrictLeft ω).IntertwiningMap π ≃ₗ[ℂ] Module.Dual ℂ (BigThetaSpace ω π) :=
  { homToThetaDual ω π with
    invFun := thetaDualToHom ω π hω hπ hG
    left_inv := fun f => Representation.IntertwiningMap.ext (LinearMap.ext fun s => by
      change (admissibleBidualEquiv π hπ hG).symm (thetaFunctional ω π hω _ s) = f s
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.ext fun l => rfl))
    right_inv := fun ℓ => Representation.Coinvariants.hom_ext <| TensorProduct.ext' fun s l => by
      change l.val ((admissibleBidualEquiv π hπ hG).symm (thetaFunctional ω π hω ℓ s)) =
        ℓ (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l))
      exact congrArg (fun y : SmoothDual (smoothContragredient π) => y.val l)
        ((admissibleBidualEquiv π hπ hG).apply_symm_apply (thetaFunctional ω π hω ℓ s)) }

theorem homEquivThetaDual_apply (f : (restrictLeft ω).IntertwiningMap π) :
    homEquivThetaDual hω hπ hG f = homToThetaDual ω π f := rfl

include hω hπ hG in
/-- **The big theta lift is non-zero exactly when `π` is a quotient of `ω|_G`** (GKT Proposition
13.18, p. 400–401). -/
theorem nontrivial_bigThetaSpace_iff :
    Nontrivial (BigThetaSpace ω π) ↔ ∃ f : (restrictLeft ω).IntertwiningMap π, f ≠ 0 := by
  rw [← Module.nontrivial_dual_iff ℂ, ← (homEquivThetaDual hω hπ hG).nontrivial_congr,
    nontrivial_iff_exists_ne 0]

end Duality

/-! ### `Hom_{G×H}(ω, π ⊠ σ) = Hom_H(Θ_ω(π), σ)` (GKT Corollary 13.8) -/

section Corollary

variable {ω π}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem fixedVectors_mono {K L : Subgroup G} (h : L ≤ K) :
    fixedVectors π K ≤ fixedVectors π L :=
  fun _ hv l => hv ⟨l, h l.2⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem range_map_fixedVectors_mono {K L : Subgroup G} (h : L ≤ K) :
    LinearMap.range (TensorProduct.map (fixedVectors π K).subtype (LinearMap.id : W →ₗ[ℂ] W)) ≤
      LinearMap.range
        (TensorProduct.map (fixedVectors π L).subtype (LinearMap.id : W →ₗ[ℂ] W)) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨TensorProduct.map (Submodule.inclusion (fixedVectors_mono h)) LinearMap.id y, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

variable (hG : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

include hG in
omit [IsTopologicalGroup G] in
/-- Every tensor of `π ⊗ W`, `π` smooth, lies in `π^K ⊗ W` for a compact open subgroup `K`. -/
theorem exists_mem_range_map_fixedVectors (hπs : IsSmooth π) (x : V ⊗[ℂ] W) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      x ∈ LinearMap.range (TensorProduct.map (fixedVectors π K.toSubgroup).subtype
        (LinearMap.id : W →ₗ[ℂ] W)) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨K, hK⟩ := hπs v
    obtain ⟨L, hL, hLK⟩ := hG K
    exact ⟨L, hL, ⟨⟨v, fun k => hK ⟨k, hLK k.2⟩⟩ ⊗ₜ w, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨K, -, hxK⟩ := hx
    obtain ⟨K', -, hyK'⟩ := hy
    obtain ⟨L, hL, hLK⟩ := hG (K ⊓ K')
    refine ⟨L, hL, Submodule.add_mem _ ?_ ?_⟩
    · exact range_map_fixedVectors_mono (fun g hg => (hLK hg).1) hxK
    · exact range_map_fixedVectors_mono (fun g hg => (hLK hg).2) hyK'

variable (hπ : IsAdmissible π)

include hG hπ in
/-- **The smooth dual separates `π ⊗ W`**: a tensor killed by every `λ ⊗ 1`, `λ ∈ π^∨`, is zero. -/
theorem eq_zero_of_forall_contractLeft {x : V ⊗[ℂ] W}
    (hx : ∀ l : SmoothDual π, contractLeft l.val x = 0) : x = 0 := by
  obtain ⟨K, hK, y, rfl⟩ := exists_mem_range_map_fixedVectors hG hπ.1 x
  have : Module.Finite ℂ (fixedVectors π K.toSubgroup) := hπ.2 K
  let b := Module.finBasis ℂ (fixedVectors π K.toSubgroup)
  have hy : y = 0 := by
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    rw [map_zero]
    ext i
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply, Finsupp.coe_zero, Pi.zero_apply]
    obtain ⟨μ, hμ⟩ := (smoothDualFixedRestriction_bijective π hπ.1 K hK).2 (b.coord i)
    have h := hx μ.val
    rw [contractLeft_map] at h
    have e : μ.val.val ∘ₗ (fixedVectors π K.toSubgroup).subtype = b.coord i := hμ
    rw [e] at h
    exact h
  rw [hy, map_zero]

variable (hω : IsSmooth (restrictLeft ω))

include hω hπ hG in
/-- The tensor `∑ᵢ bᵢ ⊗ L[s ⊗ μᵢ]`, for a basis `b` of `π^K` (`K` compact open fixing `s`) and
smooth functionals `μᵢ` restricting to the dual basis, satisfies `(λ ⊗ 1) x = L[s ⊗ λ]`. -/
theorem contractLeft_sum_basis (L : BigThetaSpace ω π →ₗ[ℂ] W) {s : S} {K : OpenSubgroup G}
    (hs : ∀ k : K, ω (MonoidHom.inl G H (k : G)) s = s) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (fixedVectors π K.toSubgroup))
    (μ : ι → fixedVectors (V := SmoothDual π) (smoothContragredient π) K.toSubgroup)
    (hμ : ∀ i, smoothDualFixedRestriction π K.toSubgroup (μ i) = b.coord i) (l : SmoothDual π) :
    contractLeft l.val (∑ i, ((b i : fixedVectors π K.toSubgroup) : V) ⊗ₜ[ℂ]
      L (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] (μ i).val))) =
      L (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l)) := by
  have hμ' : ∀ i v (hv : v ∈ fixedVectors π K.toSubgroup), (μ i).val.val v = b.coord i ⟨v, hv⟩ :=
    fun i v hv => LinearMap.congr_fun (hμ i) ⟨v, hv⟩
  set m : SmoothDual π := ∑ i, l.val (b i) • (μ i).val with hm
  have hlin : contractLeft l.val (∑ i, ((b i : fixedVectors π K.toSubgroup) : V) ⊗ₜ[ℂ]
      L (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] (μ i).val))) =
      L (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] m)) := by
    rw [map_sum, hm, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [contractLeft_tmul, TensorProduct.tmul_smul, map_smul, map_smul]
  rw [hlin, ← sub_eq_zero, ← map_sub, ← map_sub, ← TensorProduct.tmul_sub,
    ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro w
  set f := thetaDualToHom ω π hω hπ hG (w ∘ₗ L)
  have key : w (L (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] (m - l)))) = (m - l).val (f s) :=
    (LinearMap.congr_fun ((homEquivThetaDual hω hπ hG).apply_symm_apply (w ∘ₗ L))
      (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] (m - l)))).symm
  have hv : f s ∈ fixedVectors π K.toSubgroup := fun k => by
    change π (k : G) (f s) = f s
    rw [← Representation.IntertwiningMap.isIntertwining (restrictLeft ω) π f]
    exact congrArg f (hs k)
  rw [key, Submodule.coe_sub, LinearMap.sub_apply, sub_eq_zero, hm, Submodule.coe_sum,
    LinearMap.sum_apply]
  simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul, hμ' _ _ hv]
  have := LinearMap.congr_fun (b.sum_dual_apply_smul_coord
    (l.val ∘ₗ (fixedVectors π K.toSubgroup).subtype)) ⟨f s, hv⟩
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.comp_apply, Submodule.subtype_apply] using this

include hω hπ hG in
/-- For an `H`-map `L` out of `Θ_ω(π)` and `s ∈ S`, the map `λ ↦ L[s ⊗ λ]` is `λ ⊗ 1` of a tensor
of `π ⊗ W` (the tensor is built on `π^K ⊗ W`, `K` fixing `s`). -/
theorem exists_contractLeft_eq (L : BigThetaSpace ω π →ₗ[ℂ] W) (s : S) :
    ∃ x : V ⊗[ℂ] W, ∀ l : SmoothDual π,
      contractLeft l.val x = L (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l)) := by
  obtain ⟨K₀, hK₀⟩ := hω s
  obtain ⟨K, hK, hKK₀⟩ := hG K₀
  have hs : ∀ k : K, ω (MonoidHom.inl G H (k : G)) s = s := fun k => hK₀ ⟨k, hKK₀ k.2⟩
  have : Module.Finite ℂ (fixedVectors π K.toSubgroup) := hπ.2 K
  let b := Module.finBasis ℂ (fixedVectors π K.toSubgroup)
  choose μ hμ using fun i => (smoothDualFixedRestriction_bijective π hπ.1 K hK).2 (b.coord i)
  exact ⟨_, contractLeft_sum_basis hG hπ hω L hs b μ hμ⟩

variable (σ : Representation ℂ H W)

variable (ω π) in
/-- The bilinear map `(s, λ) ↦ (λ ⊗ 1)(F s)` of a `G × H`-map `F : ω → π ⊠ σ`. -/
def homBilin (F : ω.IntertwiningMap (outerTensor π σ)) :
    S →ₗ[ℂ] SmoothDual π →ₗ[ℂ] W :=
  LinearMap.mk₂ ℂ (fun s l => contractLeft l.val (F s))
    (fun s s' l => by rw [map_add, map_add])
    (fun c s l => by rw [map_smul, map_smul])
    (fun s l l' => by rw [Submodule.coe_add, contractLeft_add])
    (fun c s l => by rw [Submodule.coe_smul, contractLeft_smul])

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem outerTensor_inl (g : G) (x : V ⊗[ℂ] W) :
    outerTensor π σ (MonoidHom.inl G H g) x = TensorProduct.map (π g) LinearMap.id x := by
  change TensorProduct.map (π g) (σ 1) x = _
  rw [map_one]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem outerTensor_inr (h : H) (x : V ⊗[ℂ] W) :
    outerTensor π σ (MonoidHom.inr G H h) x = TensorProduct.map LinearMap.id (σ h) x := by
  change TensorProduct.map (π 1) (σ h) x = _
  rw [map_one]
  rfl

theorem dual_comp_eq (g : G) (l : SmoothDual π) :
    l.val ∘ₗ π g = (smoothContragredient π g⁻¹ l).val :=
  LinearMap.ext fun v => by rw [LinearMap.comp_apply, smoothContragredient_apply_apply, inv_inv]

variable (ω π) in
/-- **`F ↦ ([s ⊗ λ] ↦ (λ ⊗ 1)(F s))`**, from `Hom_{G×H}(ω, π ⊠ σ)` to `Hom_H(Θ_ω(π), σ)`
(GKT Corollary 13.8). -/
def homToThetaHom (F : ω.IntertwiningMap (outerTensor π σ)) :
    (bigTheta ω π).IntertwiningMap σ where
  toLinearMap := Representation.Coinvariants.lift _ (TensorProduct.lift (homBilin ω π σ F))
    (fun g => TensorProduct.ext' fun s l => by
      change contractLeft (smoothContragredient π g l).val (F (ω (MonoidHom.inl G H g) s)) =
        contractLeft l.val (F s)
      rw [show F (ω (MonoidHom.inl G H g) s) = outerTensor π σ (MonoidHom.inl G H g) (F s) from
        Representation.IntertwiningMap.isIntertwining _ _ F _ s, outerTensor_inl,
        contractLeft_map, dual_comp_eq, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply])
  isIntertwining' h := Representation.Coinvariants.hom_ext <| TensorProduct.ext' fun s l => by
    change contractLeft l.val (F (ω (MonoidHom.inr G H h) s)) = σ h (contractLeft l.val (F s))
    rw [show F (ω (MonoidHom.inr G H h) s) = outerTensor π σ (MonoidHom.inr G H h) (F s) from
      Representation.IntertwiningMap.isIntertwining _ _ F _ s, outerTensor_inr,
      contractLeft_map_right]

theorem homToThetaHom_mk (F : ω.IntertwiningMap (outerTensor π σ)) (s : S) (l : SmoothDual π) :
    homToThetaHom ω π σ F (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l)) =
      contractLeft l.val (F s) := rfl

variable {σ}

variable (hω : IsSmooth (restrictLeft ω))

variable (ω π) in
/-- The tensor `x ∈ π ⊗ W` with `(λ ⊗ 1) x = L[s ⊗ λ]` (`exists_contractLeft_eq`). -/
def thetaTensorOf (L : (bigTheta ω π).IntertwiningMap σ) (s : S) : V ⊗[ℂ] W :=
  Classical.choose (exists_contractLeft_eq hG hπ hω L.toLinearMap s)

theorem contractLeft_thetaTensorOf (L : (bigTheta ω π).IntertwiningMap σ) (s : S)
    (l : SmoothDual π) :
    contractLeft l.val (thetaTensorOf ω π hG hπ hω L s) =
      L (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l)) :=
  Classical.choose_spec (exists_contractLeft_eq hG hπ hω L.toLinearMap s) l

theorem eq_thetaTensorOf (L : (bigTheta ω π).IntertwiningMap σ) (s : S) {x : V ⊗[ℂ] W}
    (hx : ∀ l : SmoothDual π, contractLeft l.val x = L (Representation.Coinvariants.mk _
      (s ⊗ₜ[ℂ] l))) :
    x = thetaTensorOf ω π hG hπ hω L s := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_contractLeft hG hπ fun l => by
    rw [map_sub, hx, contractLeft_thetaTensorOf, sub_self]

variable (ω π) in
/-- The inverse of `homToThetaHom`: `L ↦ (s ↦ the tensor x with (λ ⊗ 1) x = L[s ⊗ λ])`. -/
def thetaHomToHom (L : (bigTheta ω π).IntertwiningMap σ) :
    ω.IntertwiningMap (outerTensor π σ) where
  toFun := thetaTensorOf ω π hG hπ hω L
  map_add' s s' := (eq_thetaTensorOf hG hπ hω L (s + s') fun l => by
    rw [map_add, contractLeft_thetaTensorOf, contractLeft_thetaTensorOf,
      TensorProduct.add_tmul, map_add, map_add]).symm
  map_smul' c s := (eq_thetaTensorOf hG hπ hω L (c • s) fun l => by
    rw [map_smul, contractLeft_thetaTensorOf, RingHom.id_apply, ← TensorProduct.smul_tmul',
      map_smul, map_smul]).symm
  isIntertwining' p := LinearMap.ext fun s => by
    change thetaTensorOf ω π hG hπ hω L (ω p s) =
      outerTensor π σ p (thetaTensorOf ω π hG hπ hω L s)
    have hp : p = MonoidHom.inr G H p.2 * MonoidHom.inl G H p.1 := by ext <;> simp
    refine (eq_thetaTensorOf hG hπ hω L (ω p s) fun l => ?_).symm
    rw [hp, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, outerTensor_inl,
      outerTensor_inr, contractLeft_map_right, contractLeft_map, dual_comp_eq,
      contractLeft_thetaTensorOf, ← mk_tmul_inl, ← bigTheta_mk,
      Representation.IntertwiningMap.isIntertwining]

/-- **`Hom_{G×H}(ω, π ⊠ σ) = Hom_H(Θ_ω(π), σ)`** (GKT Corollary 13.8, p. 393), for an admissible
`π` of a group with a cofinal family of compact open subgroups, `ω` smooth on `G`, and any
representation `σ` of `H`. -/
def homEquivThetaHom :
    ω.IntertwiningMap (outerTensor π σ) ≃ₗ[ℂ] (bigTheta ω π).IntertwiningMap σ where
  toFun := homToThetaHom ω π σ
  map_add' F F' := Representation.IntertwiningMap.ext <| Representation.Coinvariants.hom_ext <|
    TensorProduct.ext' fun s l => by
      change contractLeft l.val (F s + F' s) = contractLeft l.val (F s) + contractLeft l.val (F' s)
      rw [map_add]
  map_smul' c F := Representation.IntertwiningMap.ext <| Representation.Coinvariants.hom_ext <|
    TensorProduct.ext' fun s l => by
      change contractLeft l.val (c • F s) = c • contractLeft l.val (F s)
      rw [map_smul]
  invFun := thetaHomToHom ω π hG hπ hω
  left_inv F := Representation.IntertwiningMap.ext <| LinearMap.ext fun s =>
    (eq_thetaTensorOf hG hπ hω _ s fun _ => rfl).symm
  right_inv L := Representation.IntertwiningMap.ext <| Representation.Coinvariants.hom_ext <|
    TensorProduct.ext' fun s l => contractLeft_thetaTensorOf hG hπ hω L s l

theorem homEquivThetaHom_apply_mk (F : ω.IntertwiningMap (outerTensor π σ)) (s : S)
    (l : SmoothDual π) :
    homEquivThetaHom hG hπ hω F (Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l)) =
      contractLeft l.val (F s) := rfl

variable (ω π) in
/-- **The map `S → π ⊗ Θ_ω(π)`** of GKT Proposition 13.7 (p. 393): the `G × H`-map corresponding
to the identity of `Θ_ω(π)` under Corollary 13.8, characterized by
`(λ ⊗ 1)(φ s) = [s ⊗ λ]` (`contractLeft_isotypicQuotientMap`). -/
def isotypicQuotientMap : ω.IntertwiningMap (outerTensor π (bigTheta ω π)) :=
  thetaHomToHom ω π hG hπ hω (Representation.IntertwiningMap.id (bigTheta ω π))

theorem contractLeft_isotypicQuotientMap (s : S) (l : SmoothDual π) :
    contractLeft l.val (isotypicQuotientMap ω π hG hπ hω s) =
      Representation.Coinvariants.mk _ (s ⊗ₜ[ℂ] l) :=
  contractLeft_thetaTensorOf hG hπ hω _ s l

/-- **The kernel of `S → π ⊗ Θ_ω(π)` is `S(π)`** (GKT Proposition 13.7, p. 393, the part
`ker φ = S(π)`): so `S / S(π)` embeds into `π ⊗ Θ_ω(π)`. -/
theorem ker_isotypicQuotientMap :
    LinearMap.ker (isotypicQuotientMap ω π hG hπ hω).toLinearMap = isotypicKernel ω π := by
  ext s
  rw [LinearMap.mem_ker, mem_isotypicKernel]
  change isotypicQuotientMap ω π hG hπ hω s = 0 ↔ _
  constructor
  · intro h f
    apply smoothBidual_injective_of_compact_cofinal hG π hπ.1
    rw [map_zero]
    refine Subtype.ext (LinearMap.ext fun l => ?_)
    change l.val (f s) = 0
    have h1 := contractLeft_isotypicQuotientMap hG hπ hω s l
    rw [h, map_zero] at h1
    rw [← homToThetaDual_mk ω π f s l, ← h1, map_zero]
  · intro h
    refine eq_zero_of_forall_contractLeft hG hπ fun l => ?_
    rw [contractLeft_isotypicQuotientMap, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro ℓ
    obtain ⟨f, rfl⟩ := (homEquivThetaDual hω hπ hG).surjective ℓ
    rw [homEquivThetaDual_apply, homToThetaDual_mk, h f, map_zero]

/-- `S / S(π) → π ⊗ Θ_ω(π)` is injective (GKT Proposition 13.7). -/
theorem isotypicQuotientMap_eq_iff {s s' : S} :
    isotypicQuotientMap ω π hG hπ hω s = isotypicQuotientMap ω π hG hπ hω s' ↔
      s - s' ∈ isotypicKernel ω π := by
  rw [← ker_isotypicQuotientMap hG hπ hω, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

end Corollary

/-! ### Surjectivity of `S → π ⊗ Θ_ω(π)` for irreducible `π` (GKT Proposition 13.7) -/

section Surjective

variable {π}
variable (hG : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

include hG in
omit [IsTopologicalGroup G] in
/-- **Schur's lemma for admissible irreducible representations**: a `G`-endomorphism of an
admissible irreducible `π` is a scalar (it has an eigenvalue on the finite-dimensional space of
vectors fixed by a compact open subgroup, and the eigenspace is a non-zero subrepresentation). -/
theorem exists_eq_smul_of_isAdmissible (hπ : IsAdmissible π) (hirr : π.IsIrreducible)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v := by
  have hne : (⊥ : Subrepresentation π) ≠ ⊤ := bot_ne_top
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra! h
    refine hne (le_antisymm bot_le fun w _ => ?_)
    rw [h w]
    exact (⊥ : Submodule ℂ V).zero_mem
  obtain ⟨K, hK⟩ := hπ.1 v
  obtain ⟨L, -, hLK⟩ := hG K
  have hvL : v ∈ fixedVectors π L.toSubgroup := fun l => hK ⟨l, hLK l.2⟩
  have : Module.Finite ℂ (fixedVectors π L.toSubgroup) := hπ.2 L
  have : Nontrivial (fixedVectors π L.toSubgroup) :=
    ⟨⟨⟨v, hvL⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  let TL : Module.End ℂ (fixedVectors π L.toSubgroup) :=
    (T.toLinearMap.comp (fixedVectors π L.toSubgroup).subtype).codRestrict _ fun x l => by
      change π l (T x.val) = T x.val
      rw [← Representation.IntertwiningMap.isIntertwining]
      exact congrArg T (x.2 l)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue TL
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  let P : Subrepresentation π :=
    { toSubmodule := LinearMap.ker (T.toLinearMap - c • LinearMap.id)
      apply_mem_toSubmodule := fun g y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
        change T (π g y) - c • π g y = 0
        rw [Representation.IntertwiningMap.isIntertwining, ← map_smul, ← map_sub]
        exact (congrArg (π g) hy).trans (map_zero _) }
  have hP : P ≠ ⊥ := fun h => hx.2 <| Subtype.ext <| by
    have hmem : x.val ∈ P := by
      change x.val ∈ LinearMap.ker (T.toLinearMap - c • LinearMap.id)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero]
      exact congrArg Subtype.val hx.apply_eq_smul
    rw [h] at hmem
    exact hmem
  refine ⟨c, fun w => ?_⟩
  have hw : w ∈ P := by rw [(IsSimpleOrder.eq_bot_or_eq_top P).resolve_left hP]; trivial
  change w ∈ LinearMap.ker (T.toLinearMap - c • LinearMap.id) at hw
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at hw

include hG in
omit [IsTopologicalGroup G] in
/-- **Density** (Jacobson's density theorem with Schur's lemma): for an admissible irreducible `π`,
every linear map `V → V` agrees on a finite set with an element of the group algebra. -/
theorem exists_asAlgebraHom_eq (hπ : IsAdmissible π) (hirr : π.IsIrreducible) (T : V →ₗ[ℂ] V)
    (s : Finset V) : ∃ r : MonoidAlgebra ℂ G, ∀ m ∈ s, π.asAlgebraHom r m = T m := by
  classical
  have : IsSimpleModule (MonoidAlgebra ℂ G) π.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule π).1 hirr
  set e := π.asModuleEquiv
  have h1 : ∀ (c : ℂ) (y : π.asModule), c • y = (algebraMap ℂ (MonoidAlgebra ℂ G) c) • y :=
    fun c y => e.injective <| by
      rw [e.map_smul, Representation.asModuleEquiv_map_smul, AlgHom.commutes,
        Module.algebraMap_end_apply]
  have hlin : ∀ (f : Module.End (MonoidAlgebra ℂ G) π.asModule) (c : ℂ) (x : π.asModule),
      f (c • x) = c • f x := fun f c x => by rw [h1, f.map_smul, ← h1]
  have hscalar : ∀ f : Module.End (MonoidAlgebra ℂ G) π.asModule, ∃ c : ℂ, ∀ x, f x = c • x := by
    intro f
    let f' : π.IntertwiningMap π :=
      { toLinearMap :=
          { toFun := fun v => e (f (e.symm v))
            map_add' := fun v w => by rw [map_add, map_add, map_add]
            map_smul' := fun c v => by rw [map_smul, hlin, map_smul]; rfl }
        isIntertwining' := fun g => LinearMap.ext fun v => by
          change e (f (e.symm (π g v))) = π g (e (f (e.symm v)))
          rw [Representation.asModuleEquiv_symm_map_rho, f.map_smul,
            Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of] }
    obtain ⟨c, hc⟩ := exists_eq_smul_of_isAdmissible hG hπ hirr f'
    refine ⟨c, fun x => e.injective ?_⟩
    have := hc (e x)
    change e (f (e.symm (e x))) = c • e x at this
    rw [LinearEquiv.symm_apply_apply] at this
    rw [this, e.map_smul]
  let F : Module.End (Module.End (MonoidAlgebra ℂ G) π.asModule) π.asModule :=
    { toFun := fun x => e.symm (T (e x))
      map_add' := fun x y => by rw [map_add, map_add, map_add]
      map_smul' := fun f x => by
        obtain ⟨c, hc⟩ := hscalar f
        change e.symm (T (e (f x))) = f (e.symm (T (e x)))
        rw [hc, hc, e.map_smul, T.map_smul, e.symm.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F (s.image e.symm)
  refine ⟨r, fun m hm => ?_⟩
  have h2 := congrArg e (hr (e.symm m) (Finset.mem_image_of_mem _ hm))
  change e (e.symm (T (e (e.symm m)))) = e (r • e.symm m) at h2
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] at h2
  exact h2.symm

variable {ω} (hπ : IsAdmissible π) (hω : IsSmooth (restrictLeft ω))

include hG hπ hω in
/-- **`S → π ⊗ Θ_ω(π)` is surjective for irreducible `π`** (GKT Proposition 13.7, p. 393; the book
uses Lemma 13.1, here replaced by the density theorem applied to `φ(s) = ∑ᵢ bᵢ ⊗ [s ⊗ μᵢ]`). -/
theorem isotypicQuotientMap_surjective (hirr : π.IsIrreducible) :
    Function.Surjective (isotypicQuotientMap ω π hG hπ hω) := by
  classical
  set φ := isotypicQuotientMap ω π hG hπ hω
  let U := LinearMap.range φ.toLinearMap
  have hstab : ∀ (r : MonoidAlgebra ℂ G) (x : V ⊗[ℂ] BigThetaSpace ω π), x ∈ U →
      TensorProduct.map (π.asAlgebraHom r) LinearMap.id x ∈ U := by
    intro r x hx
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      obtain ⟨s, rfl⟩ := hx
      refine ⟨ω (MonoidHom.inl G H g) s, ?_⟩
      rw [Representation.asAlgebraHom_of]
      change φ (ω (MonoidHom.inl G H g) s) = _
      rw [Representation.IntertwiningMap.isIntertwining, outerTensor_inl]
      rfl
    | add r r' hr hr' =>
      rw [map_add, TensorProduct.map_add_left, LinearMap.add_apply]
      exact U.add_mem hr hr'
    | smul c r hr =>
      rw [map_smul, TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact U.smul_mem c hr
  have key : ∀ (v : V) (s : S) (l : SmoothDual π),
      v ⊗ₜ[ℂ] Representation.Coinvariants.mk (thetaTensor ω π) (s ⊗ₜ[ℂ] l) ∈ U := by
    intro v s l
    obtain ⟨K₀, hK₀⟩ := hω s
    obtain ⟨K, hK, hKK₀⟩ := hG K₀
    have hs : ∀ k : K, ω (MonoidHom.inl G H (k : G)) s = s := fun k => hK₀ ⟨k, hKK₀ k.2⟩
    have : Module.Finite ℂ (fixedVectors π K.toSubgroup) := hπ.2 K
    let b := Module.finBasis ℂ (fixedVectors π K.toSubgroup)
    choose μ hμ using fun i => (smoothDualFixedRestriction_bijective π hπ.1 K hK).2 (b.coord i)
    have hsum := contractLeft_sum_basis hG hπ hω LinearMap.id hs b μ hμ
    have hφs : φ s = ∑ i, ((b i : fixedVectors π K.toSubgroup) : V) ⊗ₜ[ℂ]
        Representation.Coinvariants.mk (thetaTensor ω π) (s ⊗ₜ[ℂ] (μ i).val) :=
      (eq_thetaTensorOf hG hπ hω (Representation.IntertwiningMap.id (bigTheta ω π)) s
        fun l => hsum l).symm
    have hl : Representation.Coinvariants.mk (thetaTensor ω π) (s ⊗ₜ[ℂ] l) =
        ∑ i, l.val (b i) • Representation.Coinvariants.mk (thetaTensor ω π)
          (s ⊗ₜ[ℂ] (μ i).val) := by
      have h' := hsum l
      rw [LinearMap.id_apply] at h'
      rw [← h', map_sum]
      exact Finset.sum_congr rfl fun i _ => contractLeft_tmul _ _ _
    rw [hl, TensorProduct.tmul_sum]
    refine U.sum_mem fun j _ => ?_
    rw [TensorProduct.tmul_smul]
    refine U.smul_mem _ ?_
    obtain ⟨T, hT⟩ := LinearMap.exists_extend ((b.coord j).smulRight v)
    have hTb : ∀ i, T (b i : V) = if i = j then v else 0 := fun i => by
      have := LinearMap.congr_fun hT (b i)
      rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smulRight_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this
      rw [this]
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hG hπ hirr T
      (Finset.univ.image fun i => ((b i : fixedVectors π K.toSubgroup) : V))
    have hmap : TensorProduct.map (π.asAlgebraHom r) LinearMap.id (φ s) =
        v ⊗ₜ[ℂ] Representation.Coinvariants.mk (thetaTensor ω π) (s ⊗ₜ[ℂ] (μ j).val) := by
      rw [hφs, map_sum, Finset.sum_eq_single j]
      · rw [TensorProduct.map_tmul, LinearMap.id_apply,
          hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hTb]
        simp
      · intro i _ hij
        rw [TensorProduct.map_tmul, LinearMap.id_apply,
          hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hTb]
        simp [hij]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [← hmap]
    exact hstab r _ ⟨s, rfl⟩
  have hU : U = ⊤ := by
    rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨v, θ, rfl⟩
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ θ
    induction y using TensorProduct.inductionOn with
    | tmul s l => exact key v s l
    | add y y' hy hy' =>
      rw [map_add, TensorProduct.tmul_add]
      exact U.add_mem hy hy'
  intro x
  obtain ⟨s, hs⟩ : x ∈ U := hU ▸ Submodule.mem_top
  exact ⟨s, hs⟩

include hG hπ hω in
/-- **`S / S(π) ≅ π ⊗ Θ_ω(π)`** (GKT Proposition 13.7, p. 393), induced by the `G × H`-map
`isotypicQuotientMap`, for an admissible irreducible `π`: the maximal `π`-isotypic quotient of `ω`
is `π ⊗ Θ_ω(π)`. -/
def isotypicQuotientEquiv (hirr : π.IsIrreducible) :
    (S ⧸ isotypicKernel ω π) ≃ₗ[ℂ] V ⊗[ℂ] BigThetaSpace ω π :=
  (Submodule.quotEquivOfEq _ _ (ker_isotypicQuotientMap hG hπ hω).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (isotypicQuotientMap_surjective hG hπ hω hirr))

theorem isotypicQuotientEquiv_mk (hirr : π.IsIrreducible) (s : S) :
    isotypicQuotientEquiv hG hπ hω hirr (Submodule.Quotient.mk s) =
      isotypicQuotientMap ω π hG hπ hω s := rfl

end Surjective

end Theta

end Langlands
