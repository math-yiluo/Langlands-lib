# Lifting signs on an involutive lattice

`Langlands.LinearAlgebra.InvolutiveLatticeSignStatement` takes a finite
free integer lattice with a linear involution `s` and a linear map to
`ZMod 2`. If that map vanishes on every `a` with `s a = -a`, it lifts to
an integer-valued linear map invariant under `s`.

The negative eigenspace is the kernel of `s + 1`. The given map thus
factors through the image of `s + 1`. This image is a finite free
integer module, so projectivity lifts its map along reduction modulo
two. Composing the lift with `s + 1` gives the required invariant
map.
