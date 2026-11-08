# Separating a point of a finite fibre by a relatively clopen neighborhood

Author: Worker 36.

This module proves the topological step of Berkovich's Lemma 3.1.2. Given a
finite fibre whose surroundings are covered by finitely many compact Hausdorff
pieces, any point of the fibre has an arbitrarily small open neighborhood that
is relatively clopen in the preimage of some open neighborhood of the image
point. Only general topology is used. The analytic application, to finite
morphisms of analytic spaces, is separate.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Lemma 3.1.2, printed pp.54–55 / PDF pp.51–52, states that if a morphism is
finite at a point, the neighborhoods in Definition 3.1.1 can be found
arbitrarily small. Its proof says: "We may assume that the morphism `φ` is
finite. Let `x = φ(y)` and let `φ⁻¹(x) = {y₁ = y, y₂, …, yₙ}`. Since the map
`|Y| → |X|` is compact, we can find a sufficiently small open neighborhood `𝒰`
of `x` such that `φ⁻¹(𝒰) = ∐ᵢ₌₁ⁿ 𝒱ᵢ`, where `yᵢ ∈ 𝒱ᵢ` and `𝒱ᵢ ∩ 𝒱ⱼ = ∅` for
`i ≠ j`."

`exists_isClopenOver_of_finite_fibre` is a derived topological version of
this step. It separates the one point `y` from the rest of the preimage of
`𝒰`, which is the part of the argument the lemma needs. It assumes compactness
and Hausdorffness of finitely many pieces rather than compactness of the whole
map, so the ambient spaces need not be Hausdorff.

## The clopen condition

`IsClopenOver f Y' x O 𝒰` says that `O` and `𝒰` are open, `O ⊆ Y'`,
`x ∈ 𝒰`, and `Y' ∩ f⁻¹(𝒰) ∩ closure O ⊆ O`. Then `O ∩ f⁻¹(𝒰)` is open and
closed in `Y' ∩ f⁻¹(𝒰)`, and its intersection with any subset of
`Y' ∩ f⁻¹(𝒰)` is relatively open and closed there.

## A closed trace lemma

`exists_isClosed_inter_eq_of_isCompact`: if `H` is a subset with Hausdorff
subspace topology and `K ⊆ H` is compact, then `K = t ∩ H` for a closed set `t`
of the ambient space. In the subspace `H`, the preimage of `K` is compact,
hence closed, and closed sets of a subspace are traces of closed sets.

## The separation theorem

Let `f : Y → X` be continuous and `Y'` open. Let finitely many compact sets
`W k` contain `x`, lie in a subset `H` with Hausdorff subspace topology, and
have union a neighborhood of `x`. Suppose each piece `P k = Y' ∩ f⁻¹(W k)` is
compact and Hausdorff, and the fibre `F = Y' ∩ f⁻¹{x}` is finite. Let `y ∈ F`
and let `V₀` be a neighborhood of `y`. Then there are `O` and `𝒰` with
`IsClopenOver f Y' x O 𝒰`, `y ∈ O ⊆ V₀` and `𝒰 ⊆ ⋃ k, W k`.

1. Write `W k = t k ∩ H` with `t k` closed. Let `N₀` be the interior of the
   union of the `W k`, so `N₀ ⊆ H`. A point `p ∈ Y'` with `f p ∈ N₀` and
   `f p ∈ t k` lies in `P k`.
2. In each compact Hausdorff, hence regular, piece `P k`, the point `y` has a
   closed neighborhood `D` that avoids the finite closed set `F ∖ {y}` and
   lies in `V₀`. The interior of `D` is the trace of an ambient open set
   `G k`. Let `C k` be the closure of that interior in `P k`. Then `C k` is
   compact, contained in `P k`, meets `F` only in `y`, and contains
   `closure (G k ∩ P k) ∩ P k`.
3. Let `O = (Y' ∩ f⁻¹(N₀)) ∩ ⋂ k, ((f⁻¹ (t k))ᶜ ∪ G k)`. It is open and
   contains `y`. Every point of `O` lies in some `G k ∩ P k ⊆ V₀`.
4. A point `p` of the closure of `O` with `p ∈ Y'` and image in `N₀` lies in
   some `C k`. It is in the closure of some `G k ∩ P k`, so its image lies in
   the closed set `t k`. Since the image also lies in `N₀ ⊆ H`, it lies in
   `t k ∩ H = W k`. Together with `p ∈ Y'` this gives `p ∈ P k`, and the
   closure of `G k ∩ P k` meets `P k` inside `C k`. The membership `p ∈ Y'` is
   needed: the ambient spaces need not be Hausdorff, and a point outside `Y'`
   can lie in the closure of `O` over `N₀` without lying in any `C k`.
5. The set `Z = ⋃ k, f(C k ∖ O)` is compact, contained in `H`, and does not
   contain `x`: a point of `C k` over `x` is `y`, which lies in `O`. Write
   `Z = T ∩ H` with `T` closed, and set `𝒰 = N₀ ∩ Tᶜ`. It is open, and it
   contains `x`.
6. A point of `Y' ∩ f⁻¹(𝒰)` in the closure of `O` lies in some `C k`. If it
   were not in `O`, its image would lie in `Z ⊆ T`, which contradicts
   `f p ∈ 𝒰`.

## Scope

This is general topology. The finiteness of fibres of finite morphisms, the
analytic structure of the clopen pieces, and Lemma 3.1.2 itself for analytic
spaces are not proved here.
